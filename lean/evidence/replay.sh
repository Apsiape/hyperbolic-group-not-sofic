#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/.."
mkdir -p evidence
out=evidence/leanchecker.log
tmp=evidence/leanchecker.tmp
: > "$out"
find vendor/finite-lean/FiniteLean -name '*.lean' | sort | while IFS= read -r f; do
  f=${f#vendor/finite-lean/}
  m=$(printf '%s' "${f%.lean}" | tr / .)
  start=$(date +%s)
  if lake env leanchecker "$m" > "$tmp" 2>&1; then st=ok; else st=FAIL; fi
  printf '%s %s %ss %s\n' "$st" "$m" "$(( $(date +%s) - start ))" "$(head -c 300 "$tmp" | tr '\n' ' ')" >> "$out"
done
printf 'DONE\n' >> "$out"
