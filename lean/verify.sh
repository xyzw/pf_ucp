#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
exec python3 verify_scope.py --jobs "${PF_HK_VERIFY_JOBS:-1}" PfHk
