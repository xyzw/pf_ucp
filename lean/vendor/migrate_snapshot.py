#!/usr/bin/env python3
"""Validate historical artifacts after vendoring without running the compiler.

The output is an input to verify_scope.py --reuse-snapshot, not a new Lean
verification result. Every source and artifact must match an archived record.
"""

import hashlib
import json
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor"
HASH_PATTERN = re.compile(r"[0-9a-f]{64}")


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pointer(parts):
    return "/" + "/".join(str(p).replace("~", "~0").replace("/", "~1")
                            for p in parts)


def module_source(value):
    """Normalize historical module and source path spellings."""
    if not isinstance(value, str):
        return None
    if re.fullmatch(r"GptLean(?:\.[A-Za-z0-9_]+)+", value):
        return value.replace(".", "/") + ".lean"
    match = re.search(r"(?:^|/)(GptLean/[A-Za-z0-9_/]+\.lean)$", value)
    return match.group(1) if match else None


def success(record):
    if any(record.get(key) == 0 for key in
           ("exit_code", "observed_exit_code", "source_exit_code")):
        return True
    status = record.get("status")
    return isinstance(status, str) and status.startswith("passed")


def evidence_metadata(record):
    keys = ("status", "exit_code", "observed_exit_code", "source_exit_code",
            "evidence_kind", "source_unchanged", "source_unchanged_during_check",
            "dependencies_unchanged", "dependencies_unchanged_during_check",
            "historical_hash_matches", "historical_artifact_hash_matches")
    return {key: record[key] for key in keys if key in record}


def historical_pairs(snapshot):
    """Index exact pairs and their nearest recorded successful check."""
    pairs = defaultdict(list)

    def walk(value, path=(), successful_ancestors=()):
        if isinstance(value, dict):
            own_success = success(value)
            ancestors = successful_ancestors
            if own_success:
                ancestors += ((path, value),)
            source = next((name for key in ("source_path", "source", "module")
                           if (name := module_source(value.get(key)))), None)
            if source is None:
                source = next((name for part in reversed(path)
                               if (name := module_source(part))), None)
            source_hash = value.get("source_sha256")
            artifact_hash = value.get("artifact_sha256", value.get("olean_sha256"))
            if (source is not None and isinstance(source_hash, str)
                    and HASH_PATTERN.fullmatch(source_hash)
                    and isinstance(artifact_hash, str)
                    and HASH_PATTERN.fullmatch(artifact_hash) and ancestors):
                supporting_path, supporting_record = ancestors[-1]
                pairs[source, source_hash, artifact_hash].append({
                    "evidence_kind": ("historical-source-check" if own_success
                                      else "historical-dependency-fingerprint"),
                    "record_json_pointer": pointer(path),
                    "record_metadata": evidence_metadata(value),
                    "supporting_check_json_pointer": pointer(supporting_path),
                    "supporting_check_metadata": evidence_metadata(supporting_record),
                })
            for key, child in value.items():
                walk(child, path + (key,), ancestors)
        elif isinstance(value, list):
            for index, child in enumerate(value):
                walk(child, path + (index,), successful_ancestors)

    walk(snapshot)
    return pairs


def normalized_manifest(manifest):
    require(isinstance(manifest, dict), "Manifest must be a JSON object.")
    packages = manifest.get("packages")
    require(isinstance(packages, list), "Manifest must contain a packages list.")
    names = [package.get("name") for package in packages]
    require(all(isinstance(name, str) for name in names), "Invalid package name.")
    require(len(names) == len(set(names)), "Duplicate package names in manifest.")
    require("mathlib" in names, "Pinned mathlib package is missing.")
    require(all(package.get("type") == "git" and package.get("rev")
                for package in packages), "Every dependency must have a pinned git revision.")
    result = {key: value for key, value in manifest.items() if key != "name"}
    result["packages"] = sorted(packages, key=lambda package: package["name"])
    return result


def main():
    upstream_path = VENDOR / "GptLean_source_snapshot.json"
    provenance_path = VENDOR / "GptLean_provenance.json"
    old_manifest_path = VENDOR / "GptLean_lake-manifest.json"
    manifest_path = ROOT / "lake-manifest.json"
    old_scope_path = ROOT / "verification_history/pre_vendor_snapshot.json"
    old_log_path = ROOT / "verification_history/pre_vendor_verification.log"
    input_paths = [upstream_path, provenance_path, old_manifest_path, manifest_path,
                   old_scope_path, old_log_path, ROOT / "lean-toolchain"]
    input_hashes = {str(path.relative_to(ROOT)): digest(path) for path in input_paths}
    upstream = json.loads(upstream_path.read_text())
    provenance = json.loads(provenance_path.read_text())
    old_scope = json.loads(old_scope_path.read_text())
    old_manifest = json.loads(old_manifest_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    require(toolchain == old_scope.get("toolchain") == provenance.get("toolchain"),
            "Pinned toolchain does not match both archived records.")
    require(digest(upstream_path) == provenance.get("upstream_snapshot_sha256"),
            "Archived GptLean snapshot does not match its provenance hash.")
    require(digest(old_manifest_path) == provenance.get("upstream_manifest_sha256")
            == old_scope.get("dependency_manifest_sha256"),
            "Archived dependency manifest does not match both prior records.")
    require(digest(old_log_path) == old_scope.get("verification_log_sha256"),
            "Archived PfHk verification log does not match its snapshot.")
    require(old_manifest.get("name") == "gpt_lean" and manifest.get("name") == "pf_hk",
            "Unexpected old or new root package name.")
    require(normalized_manifest(old_manifest) == normalized_manifest(manifest),
            "Dependency manifests differ beyond their root package name.")

    vendored = {}
    for record in provenance.get("sources", []):
        source = record.get("source")
        require(module_source(source) == source and source not in vendored,
                f"Invalid or duplicate vendored source record {source!r}.")
        vendored[source] = record["source_sha256"]
    require(len(vendored) == provenance.get("source_count"),
            "Vendored source count does not match provenance.")
    disk_sources = {str(path.relative_to(ROOT)) for path in (ROOT / "GptLean").rglob("*.lean")}
    require(disk_sources == set(vendored), "Vendored files differ from the provenance list.")
    old_records = {}
    for index, record in enumerate(old_scope.get("sources", [])):
        source = record.get("source")
        require(isinstance(source, str) and source not in old_records,
                f"Invalid or duplicate previous source record {source!r}.")
        old_records[source] = index, record

    sources = subprocess.check_output(
        [sys.executable, str(ROOT / "build_order.py"), "--root", "PfHk"],
        cwd=ROOT, text=True).splitlines()
    require(len(sources) == len(set(sources)), "Build order contains duplicate sources.")
    require({source for source in sources if source.startswith("GptLean/")} == set(vendored),
            "PfHk import closure does not match the vendored GptLean selection.")
    require("PfHk.lean" in sources, "PfHk aggregate is missing from its build order.")
    pairs = historical_pairs(upstream)
    records = []
    direct_count = 0
    for source in sources:
        relative = Path(source)
        require(not relative.is_absolute() and ".." not in relative.parts
                and relative.suffix == ".lean", f"Invalid source path {source!r}.")
        artifact = ROOT / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        source_hash = digest(ROOT / relative)
        artifact_hash = digest(artifact)
        if source.startswith("GptLean/"):
            require(source_hash == vendored[source], f"Vendored source changed {source}.")
            matches = pairs.get((source, source_hash, artifact_hash), [])
            require(matches, f"No exact historical source/artifact pair with successful check provenance for {source}.")
            evidence = min(matches, key=lambda item: (
                item["evidence_kind"] != "historical-source-check",
                item["record_json_pointer"]))
            direct_count += evidence["evidence_kind"] == "historical-source-check"
            origin = {"snapshot": str(upstream_path.relative_to(ROOT)), **evidence}
        else:
            require(source in old_records, f"No pre-vendoring record for {source}.")
            index, previous = old_records[source]
            require(source_hash == previous.get("source_sha256")
                    and artifact_hash == previous.get("artifact_sha256"),
                    f"Source or artifact changed since the prior PfHk verification for {source}.")
            origin = {
                "snapshot": str(old_scope_path.relative_to(ROOT)),
                "record_json_pointer": pointer(("sources", index)),
                "evidence_kind": "previous-scope-verification",
                "previous_verification": previous.get("verification"),
                "previous_verified_at_utc": old_scope.get("verified_at_utc"),
            }
        if source != "PfHk.lean":
            records.append({"source": source, "source_sha256": source_hash,
                            "artifact_sha256": artifact_hash,
                            "verification": "historical-reuse", "historical_provenance": origin})

    for path in input_paths:
        require(digest(path) == input_hashes[str(path.relative_to(ROOT))],
                f"Input changed during migration {path.relative_to(ROOT)}.")
    for record in records:
        source = record["source"]
        artifact = ROOT / ".lake/build/lib/lean" / Path(source).with_suffix(".olean")
        require(digest(ROOT / source) == record["source_sha256"]
                and digest(artifact) == record["artifact_sha256"],
                f"Source or artifact changed during migration {source}.")
    output = {
        "migrated_at_utc": datetime.now(timezone.utc).isoformat(),
        "roots": ["PfHk"],
        "toolchain": toolchain,
        "dependency_manifest_sha256": digest(manifest_path),
        "verification_mode": "historical-artifact-migration",
        "scope": ("Exact historical source/artifact pairs migrated into the standalone project. "
                  "The pinned dependency manifests agree apart from the root package name. "
                  "No Lean compilation or axiom audit is performed by this script. "
                  "PfHk.lean is deliberately omitted so the next verification recompiles "
                  "the aggregate together with its generated ScopeAudit. "
                  "Use this record only as a reuse input to a subsequent verification."),
        "input_sha256": input_hashes,
        "migration_script_sha256": digest(Path(__file__)),
        "vendored_modules": len(vendored),
        "vendored_direct_source_check_records": direct_count,
        "vendored_dependency_fingerprint_records": len(vendored) - direct_count,
        "intentional_source_omissions": ["PfHk.lean", "ScopeAudit.lean"],
        "rebuilt_modules": [],
        "reused_modules": [str(Path(record["source"]).with_suffix("")).replace("/", ".")
                           for record in records],
        "sources": records,
    }
    destination = VENDOR / "migration_snapshot.json"
    temporary = destination.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(output, indent=2) + "\n")
    temporary.replace(destination)
    print(f"Migrated {len(records)} unchanged historical source/artifact pairs.")
    print(f"GptLean evidence includes {direct_count} source-check records and "
          f"{len(vendored) - direct_count} dependency fingerprints from successful checks.")
    print("No Lean sources were compiled or audited by this migration.")
    print(destination.relative_to(ROOT))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Migration failed. {error}") from error
