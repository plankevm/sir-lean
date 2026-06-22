#!/usr/bin/env bash
# check-report-links.sh — verify every relative Markdown link in a doc resolves
# from the doc's OWN directory, and (for `#Lnn` anchors) that the line exists.
#
# Catches the two classic review-report rots:
#   (a) links written relative to the package root instead of the doc (dead in place)
#   (b) stale line numbers after a restructure
#
# Usage:  scripts/check-report-links.sh <file.md> [more.md ...]
# Exits non-zero if any link is dead. Skips http(s)/mailto and pure-anchor (#…) links.

set -u
status=0

check_file() {
  local md="$1"
  if [[ ! -f "$md" ]]; then echo "MISSING DOC: $md"; status=1; return; fi
  local dir; dir="$(cd "$(dirname "$md")" && pwd)"
  local bad=0 total=0 target path anchor resolved want have

  while IFS= read -r target; do
    case "$target" in http://*|https://*|mailto:*|\#*) continue ;; esac
    path="${target%%#*}"
    anchor=""; [[ "$target" == *#* ]] && anchor="${target#*#}"
    [[ -z "$path" ]] && continue
    total=$((total + 1))
    resolved="$dir/$path"
    if [[ ! -e "$resolved" ]]; then
      echo "  DEAD     $md -> $target   (no file at '$path' relative to the doc)"
      bad=$((bad + 1)); continue
    fi
    if [[ "$anchor" =~ ^L([0-9]+)$ ]]; then
      want="${BASH_REMATCH[1]}"; have="$(wc -l < "$resolved")"
      if (( want > have )); then
        echo "  BADLINE  $md -> $target   (file has only $have lines)"
        bad=$((bad + 1))
      fi
    fi
  done < <(grep -oE '\]\([^)]+\)' "$md" | sed -E 's/^\]\(//; s/\)$//')

  if (( bad )); then
    echo "✗ $md: $bad dead of $total relative links"; status=1
  else
    echo "✓ $md: all $total relative links resolve"
  fi
}

if [[ $# -eq 0 ]]; then
  echo "usage: $0 <file.md> [more.md ...]" >&2; exit 2
fi
for f in "$@"; do check_file "$f"; done
exit $status
