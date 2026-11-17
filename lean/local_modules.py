"""Source discovery shared by the build order and snapshot verifier."""

from pathlib import Path
import re

LOCAL_PREFIXES = ('PfHk', 'GptLean')


def local_imports(source):
    """Read the Lean module header, allowing whitespace across line breaks.

    The shipped modules use ordinary ASCII module names. Reject unsupported
    import names instead of silently omitting their dependency edges.
    """
    # Remove nested Lean block comments and line comments before reading imports.
    clean = []
    depth = 0
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == '/-':
            depth += 1
            clean.append(' ')
            i += 2
        elif depth and pair == '-/':
            depth -= 1
            i += 2
        elif not depth and pair == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            clean.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    header = ''.join(clean)
    pos = 0
    for keyword in ('module', 'prelude'):
        match = re.compile(r'\s*' + keyword + r'\b').match(header, pos)
        if match:
            pos = match.end()
    imports = set()
    prefix = re.compile(r'\s*(?:public\s+)?(?:meta\s+)?import\b\s*(?:all\s+)?')
    name = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*(?=\s|$)')
    while True:
        match = prefix.match(header, pos)
        if not match:
            break
        module_match = name.match(header, match.end())
        if not module_match:
            raise ValueError('Unsupported or missing import name in Lean module header')
        module = module_match[0]
        if module.split('.')[0] in LOCAL_PREFIXES:
            imports.add(module)
        pos = module_match.end()
    return imports


def discover_sources(root):
    root = Path(root)
    sources = {}
    for prefix in LOCAL_PREFIXES:
        paths = list((root / prefix).rglob('*.lean'))
        aggregate = root / f'{prefix}.lean'
        if aggregate.exists():
            paths.append(aggregate)
        for path in paths:
            name = '.'.join(path.relative_to(root).with_suffix('').parts)
            sources[name] = path
    return sources


def dependency_order(root, roots):
    sources = discover_sources(root)
    ordered, active, finished = [], set(), set()

    def visit(name):
        if name in finished:
            return
        if name not in sources:
            raise ValueError(f'Missing local module {name}')
        if name in active:
            raise ValueError(f'Local import cycle at {name}')
        active.add(name)
        for dependency in sorted(local_imports(sources[name].read_text())):
            visit(dependency)
        active.remove(name)
        finished.add(name)
        ordered.append(sources[name])

    for name in sorted(roots):
        visit(name)
    return ordered
