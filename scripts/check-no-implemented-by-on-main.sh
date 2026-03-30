#!/usr/bin/env bash
set -euo pipefail

target_branch="${GITHUB_BASE_REF:-${GITHUB_REF_NAME:-}}"
if [[ -z "${target_branch}" ]]; then
  target_branch="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || true)"
fi

if [[ "${target_branch}" != "main" ]]; then
  echo "implemented_by guard skipped: target branch is '${target_branch:-unknown}'"
  exit 0
fi

pattern='@\[[[:space:]]*implemented_by\b|attribute[[:space:]]+\[[^]]*\bimplemented_by\b'

if command -v rg >/dev/null 2>&1; then
  search_cmd=(rg -n --glob '*.lean' "${pattern}" .)
else
  search_cmd=(grep -REn --include='*.lean' "${pattern}" .)
fi

if "${search_cmd[@]}"; then
  cat <<'EOF' >&2
error: `implemented_by` is forbidden on `main`.

This project allows `implemented_by` only on non-main branches.
Remove the attribute before merging or pushing to `main`.
EOF
  exit 1
fi

echo "implemented_by guard passed for main"
