#!/usr/bin/env bash
# Compile new sources against the existing checked dependency artifacts.
set -euo pipefail
cd "$(dirname "$0")"
project_root="$PWD"
build_root="$project_root/.lake/build/lib/lean"
lean_paths="$build_root"
if [[ ! -d "$project_root/.lake/packages/mathlib/.lake/build/lib/lean" ]]; then
  echo 'Install the pinned dependencies first with lake exe cache get.' >&2
  exit 1
fi
for package_path in "$project_root"/.lake/packages/*; do
  if [[ -d "$package_path/.lake/build/lib/lean" ]]; then
    lean_paths="$lean_paths:$package_path/.lake/build/lib/lean"
  fi
done
export LEAN_PATH="$lean_paths"
if [[ $# -eq 0 ]]; then
  echo 'Pass Lean sources in dependency order, or run verify.sh.' >&2
  exit 1
fi
for lean_file in "$@"; do
  module_path="${lean_file%.lean}"
  mkdir -p "$build_root/$(dirname "$module_path")"
  echo "Checking $lean_file"
  lean -j "${PF_HK_JOBS:-1}" -DautoImplicit=false -DrelaxedAutoImplicit=false \
    "$lean_file" -o "$build_root/$module_path.olean" \
    -i "$build_root/$module_path.ilean"
done
