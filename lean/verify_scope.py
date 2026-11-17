#!/usr/bin/env python3
"""Verify the local dependency closure, optionally reusing hash-matched artifacts."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from threading import Lock

from snapshot_reuse import reusable_dependency_closure
from local_modules import local_imports


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


parser = argparse.ArgumentParser()
parser.add_argument('roots', nargs='+', help='Lean module names, including the PfHk prefix')
parser.add_argument('--jobs', type=int, default=1, help='Maximum simultaneous Lean processes')
parser.add_argument('--reuse-snapshot', type=Path,
                    help='Reuse unchanged artifacts from this prior successful scope snapshot')
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be positive')
root = Path(__file__).resolve().parent
toolchain_path = root / 'lean-toolchain'
manifest_path = root / 'lake-manifest.json'
initial_toolchain = toolchain_path.read_text().strip()
initial_manifest_hash = digest(manifest_path)
reuse_snapshot_hash = None
prior_records = {}
if args.reuse_snapshot is not None:
    try:
        snapshot_bytes = args.reuse_snapshot.read_bytes()
        prior_snapshot = json.loads(snapshot_bytes)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise SystemExit(f'Cannot read reuse snapshot {args.reuse_snapshot}: {error}')
    if not isinstance(prior_snapshot, dict):
        raise SystemExit('Reuse snapshot must contain a JSON object.')
    if prior_snapshot.get('toolchain') != initial_toolchain:
        raise SystemExit('Reuse snapshot toolchain does not match the pinned lean-toolchain.')
    if prior_snapshot.get('dependency_manifest_sha256') != initial_manifest_hash:
        raise SystemExit('Reuse snapshot dependency manifest does not match lake-manifest.json.')
    records = prior_snapshot.get('sources')
    if not isinstance(records, list):
        raise SystemExit('Reuse snapshot must contain a sources list.')
    seen_sources = set()
    for record in records:
        if not isinstance(record, dict) or not isinstance(record.get('source'), str):
            raise SystemExit('Reuse snapshot contains an invalid source record.')
        source = record['source']
        if source in seen_sources:
            raise SystemExit(f'Reuse snapshot contains duplicate source records for {source}.')
        seen_sources.add(source)
        # Incomplete hash records cannot authorize reuse. They are rebuilt.
        if all(isinstance(record.get(key), str)
               and re.fullmatch(r'[0-9a-f]{64}', record[key])
               for key in ('source_sha256', 'artifact_sha256')):
            prior_records[source] = record
    reuse_snapshot_hash = hashlib.sha256(snapshot_bytes).hexdigest()

order_command = [sys.executable, str(root / 'build_order.py')]
for module in args.roots:
    order_command.extend(['--root', module])
sources = subprocess.check_output(order_command, cwd=root, text=True).splitlines()
modules = [str(Path(source).with_suffix('')).replace('/', '.') for source in sources]
audit = (root / 'Audit.lean').read_text()
audit = audit[audit.index('open Lean Elab Command in'):]
entries = ',\n'.join(f'    `{module}' for module in modules)
audit, replacements = re.subn(r'  let modules : List Name := \[.*?\]',
                             '  let modules : List Name := [\n' + entries + ']',
                             audit, count=1, flags=re.DOTALL)
if replacements != 1:
    raise SystemExit('Could not locate the audit module list')
audit_source = root / 'ScopeAudit.lean'
audit_source.write_text(''.join(f'import {module}\n' for module in args.roots)
                       + '\nset_option maxHeartbeats 0\n\n' + audit)
sources.append('ScopeAudit.lean')
initial_hashes = {source: digest(root / source) for source in sources}
module_sources = dict(zip(modules, sources[:-1]))
dependencies = {module: local_imports((root / source).read_text())
                for module, source in module_sources.items()}
matching = set()
for module, source in module_sources.items():
    record = prior_records.get(source)
    if record is None or record['source_sha256'] != initial_hashes[source]:
        continue
    artifact = root / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
    try:
        if digest(artifact) == record['artifact_sha256']:
            matching.add(module)
    except OSError:
        # Missing or unreadable artifacts must be rebuilt.
        pass
reused = reusable_dependency_closure(matching, dependencies)
rebuilt_modules = [module for module in modules if module not in reused] + ['ScopeAudit']
environment = os.environ.copy()
environment['PF_HK_JOBS'] = '1'
log_path = root / 'scope_verification.log'
with log_path.open('w') as log:
    version = subprocess.check_output(['lean', '--version'], cwd=root, text=True)
    log.write(version)
    print(version, end='', flush=True)
    if args.reuse_snapshot is not None:
        summary = (f'Hash-verified reuse of {len(reused)} local modules from '
                   f'snapshot {reuse_snapshot_hash}.\n'
                   f'Rebuilding {len(rebuilt_modules) - 1} local modules and ScopeAudit. '
                   f'The audit covers all {len(modules)} local modules.\n')
        log.write(summary)
        log.flush()
        print(summary, end='', flush=True)
    output_lock = Lock()
    def compile_source(source):
        process = subprocess.Popen(['./check.sh', source], cwd=root, env=environment,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            with output_lock:
                log.write(line)
                log.flush()
                print(line, end='', flush=True)
        return process.wait()

    pending = {module: source for module, source in module_sources.items() if module not in reused}
    completed = set(reused)
    active = {}
    result = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or active:
            if not result:
                for module, source in list(pending.items()):
                    if len(active) >= args.jobs:
                        break
                    if dependencies[module] <= completed:
                        active[pool.submit(compile_source, source)] = module
                        del pending[module]
            if not active:
                if pending and not result:
                    raise SystemExit('No dependency-ready module found')
                break
            done, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in done:
                module = active.pop(future)
                code = future.result()
                if code:
                    result = code
                else:
                    completed.add(module)
    if not result:
        result = compile_source('ScopeAudit.lean')
if result:
    raise SystemExit(result)
if any(digest(root / source) != initial_hashes[source] for source in sources):
    raise SystemExit('A source changed during verification. Rebuild the scope again.')
if toolchain_path.read_text().strip() != initial_toolchain:
    raise SystemExit('The pinned toolchain changed during verification. Rebuild the scope again.')
if digest(manifest_path) != initial_manifest_hash:
    raise SystemExit('The dependency manifest changed during verification. Rebuild the scope again.')
records = []
for source in sources:
    artifact = root / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
    try:
        artifact_hash = digest(artifact)
    except OSError as error:
        raise SystemExit(f'Cannot verify artifact {artifact}: {error}')
    module = str(Path(source).with_suffix('')).replace('/', '.')
    if module in reused and artifact_hash != prior_records[source]['artifact_sha256']:
        raise SystemExit(f'Reused artifact changed during verification: {source}. Rebuild the scope again.')
    records.append({'source': source, 'source_sha256': initial_hashes[source],
                    'artifact_sha256': artifact_hash,
                    'verification': 'reused' if module in reused else 'rebuilt'})
scope_description = (
    'Full local source dependency closure of the listed root modules, rebuilt '
    'including vendored GptLean, against pinned mathlib artifacts and audited for axioms.'
    if args.reuse_snapshot is None else
    'Full local dependency closure of the listed root modules audited for axioms, '
    'with prior source and artifact hashes verified for reused modules. All other '
    'modules and the generated audit were rebuilt using local GptLean and pinned mathlib artifacts.')
snapshot = {
    'verified_at_utc': datetime.now(timezone.utc).isoformat(),
    'roots': args.roots,
    'toolchain': initial_toolchain,
    'paper_sha256': digest(root.parent / 'pf_ucp.tex')
                    if (root.parent / 'pf_ucp.tex').is_file() else None,
    'dependency_manifest_sha256': initial_manifest_hash,
    'scope': scope_description,
    'verification_mode': 'full-rebuild' if args.reuse_snapshot is None else 'hash-verified-reuse',
    'reuse_snapshot_sha256': reuse_snapshot_hash,
    'rebuilt_modules': rebuilt_modules,
    'reused_modules': [module for module in modules if module in reused],
    'sources': records,
    'verification_log_sha256': digest(log_path),
}
(root / 'scope_snapshot.json').write_text(json.dumps(snapshot, indent=2) + '\n')
