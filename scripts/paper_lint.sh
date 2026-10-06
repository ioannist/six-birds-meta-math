#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FAILURES=0

warn() {
  printf 'WARN: %s\n' "$*" >&2
}

error() {
  printf 'ERROR: %s\n' "$*" >&2
  FAILURES=$((FAILURES + 1))
}

die() {
  error "$*"
  exit 1
}

usage() {
  printf 'usage: scripts/paper_lint.sh paper/needles_<paper>\n' >&2
}

record_grep_failures() {
  local file="$1"
  local description="$2"
  local pattern="$3"
  local hits

  hits="$(grep -nE "$pattern" "$file" || true)"
  if [[ -n "$hits" ]]; then
    error "$description in $file:"
    printf '%s\n' "$hits" >&2
  fi
}

section_files() {
  find "$PAPER_DIR/sections" -maxdepth 1 -type f -name '*.tex' | sort
}

check_argument() {
  if [[ $# -ne 1 ]]; then
    usage
    exit 1
  fi

  PAPER_DIR="${1%/}"
  if [[ ! -d "$PAPER_DIR" ]]; then
    die "paper directory does not exist: $PAPER_DIR"
  fi
}

check_structure() {
  if [[ ! -f "$PAPER_DIR/main.tex" ]]; then
    error "missing required file: $PAPER_DIR/main.tex"
  fi

  local required_dirs=(sections appendices tables figures includes)
  local dir
  for dir in "${required_dirs[@]}"; do
    if [[ ! -d "$PAPER_DIR/$dir" ]]; then
      error "missing required directory: $PAPER_DIR/$dir"
    fi
  done
}

check_body_prose_tokens() {
  local file
  local body
  local hits

  while IFS= read -r file; do
    body="$(grep -nEv '^[[:space:]]*%' "$file" || true)"

    hits="$(printf '%s\n' "$body" | grep -E 'SixBirdsMetaMath\.[A-Za-z0-9_.'\''`]+\.[A-Za-z0-9_.'\''`]+' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden Lean module identifier in body prose: $file"
      printf '%s\n' "$hits" >&2
    fi

    hits="$(printf '%s\n' "$body" | grep -E '\.jsonl?\b' | grep -Ev '\\path\{[^}]*\.jsonl?[^}]*\}' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden JSON path mention in body prose outside \\path{...}: $file"
      printf '%s\n' "$hits" >&2
    fi

    hits="$(printf '%s\n' "$body" | grep -E 'Ticket[[:space:]]*[0-9]+' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden ticket identifier in body prose: $file"
      printf '%s\n' "$hits" >&2
    fi

    hits="$(printf '%s\n' "$body" | grep -E '[A-Z][A-Z0-9]+(_[A-Z0-9]+){2,}' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden all-caps verdict token in body prose: $file"
      printf '%s\n' "$hits" >&2
    fi
  done < <(section_files)
}

check_build_log() {
  local log="$PAPER_DIR/build/main.log"

  if [[ ! -f "$log" ]]; then
    warn "build log not found at $log; skipping build-log lint"
    return
  fi

  record_grep_failures "$log" "undefined LaTeX references" 'LaTeX Warning: Reference .* undefined|There were undefined references'
  record_grep_failures "$log" "undefined LaTeX citations" 'LaTeX Warning: Citation .* undefined|There were undefined citations'
  record_grep_failures "$log" "overfull hbox warning" 'Overfull \\hbox'
  record_grep_failures "$log" "float-too-large warning" 'LaTeX Warning: Float too large'
  record_grep_failures "$log" "possible double-word cleveref artifact" 'Section Section|Appendix Appendix|Theorem Theorem|Lemma Lemma|Definition Definition|Table Table|Figure Figure'

  local underfull_hits
  underfull_hits="$(grep -nE 'Underfull \\hbox' "$log" || true)"
  if [[ -n "$underfull_hits" ]]; then
    warn "Underfull hbox warnings found in $log:"
    printf '%s\n' "$underfull_hits" >&2
  fi
}

check_label_consistency() {
  python3 - "$PAPER_DIR" <<'PY'
import pathlib
import re
import sys

try:
    import yaml
except ImportError as exc:
    raise SystemExit(f"ERROR: PyYAML is required for statements-of-record label checks: {exc}")

paper_dir = pathlib.Path(sys.argv[1])
# Per-paper SOR file takes precedence; fall back to the shared
# paper/notes/statements-of-record.yml for needles-era papers.
per_paper_record = paper_dir / "notes" / "statements-of-record.yml"
shared_record = pathlib.Path("paper/notes/statements-of-record.yml")
record_path = per_paper_record if per_paper_record.exists() else shared_record

with record_path.open("r", encoding="utf-8") as handle:
    data = yaml.safe_load(handle)

known_section_hints = {
    row["target_section_hint"]
    for row in data.get("rows", [])
    if row.get("target_section_hint") and row.get("target_section_hint") != "none"
}

failures = []
section_dir = paper_dir / "sections"
for tex_path in sorted(section_dir.glob("*.tex")):
    text = tex_path.read_text(encoding="utf-8")
    labels = re.findall(r"\\label\{(sec:[^}]+)\}", text)
    if not labels:
        failures.append(f"{tex_path}: missing section label matching \\\\label{{sec:...}}")
        continue

    allows_no_rows = "statements-of-record rows resolved here: none" in text
    for label in labels:
        if label in known_section_hints:
            continue
        if allows_no_rows:
            continue
        # Chapter-level labels and per-chapter summary/anchor labels are
        # exempt: they do not bind to a single SOR row. A label is
        # chapter-level if it has fewer than 3 colon-separated components
        # OR ends in `:summary` (the per-axis at-a-glance subsection).
        # Per-F-row labels (e.g. `sec:access:quotientality`) are checked.
        parts = label.split(":")
        if len(parts) < 3:
            continue
        if label.endswith(":summary"):
            continue
        if parts[1] == "anchor":
            # anchor-section labels like sec:anchor:closure-reality-boundary
            # are chapter-level for the anchor row; the per-row claim
            # appears in the SOR as the F53 row's target_section_hint.
            continue
        failures.append(
            f"{tex_path}: section label {label} does not appear as a "
            f"target_section_hint in {record_path}"
        )

if failures:
    for failure in failures:
        print(f"ERROR: {failure}", file=sys.stderr)
    raise SystemExit(1)
PY
}

main() {
  check_argument "$@"
  check_structure

  if [[ "$FAILURES" -eq 0 ]]; then
    check_body_prose_tokens
    check_build_log
    check_label_consistency || FAILURES=$((FAILURES + 1))
  fi

  if [[ "$FAILURES" -ne 0 ]]; then
    printf 'paper lint failed for %s with %d failure(s)\n' "$PAPER_DIR" "$FAILURES" >&2
    exit 1
  fi

  printf 'paper lint passed for %s\n' "$PAPER_DIR"
}

main "$@"
