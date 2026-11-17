#!/usr/bin/env python3
"""List the selected PfHk and vendored GptLean sources in dependency order."""

import argparse
from pathlib import Path

from local_modules import dependency_order

parser = argparse.ArgumentParser()
parser.add_argument('--root', action='append', default=[],
                    help='Root modules to check, default PfHk')
args = parser.parse_args()
root = Path(__file__).resolve().parent
try:
    sources = dependency_order(root, args.root or ['PfHk'])
except ValueError as error:
    raise SystemExit(str(error))
for source in sources:
    print(source.relative_to(root).as_posix())
