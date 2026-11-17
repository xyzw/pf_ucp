"""Legacy entry point. Verify sources before writing scope_snapshot.json."""

from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
raise SystemExit(subprocess.call(
    [sys.executable, str(root / 'verify_scope.py'), 'PfHk'], cwd=root))
