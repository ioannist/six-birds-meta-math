#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/lean/manifest.toml"
INVENTORY="$ROOT/lean/paper_inventory.toml"
TRUST_BASE="$ROOT/lean/trust_base.txt"
LOG_DIR="$ROOT/lean/.validate-logs"
EXPECTED_TOOLCHAIN="leanprover/lean4:v4.28.0"

TIER="full"
REQUIRE_FULL=0
JSON_OUT=""

usage() {
  cat <<'USAGE'
Usage: scripts/validate_lean.sh [--tier full] [--require-full] [--json PATH]

Phase 1 validates the integrated Lean project, paper inventory, and manifest.
Strict mode fails until all required entries are fully mechanized.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --tier)
      [[ $# -ge 2 ]] || { echo "error: --tier needs a value" >&2; exit 2; }
      TIER="$2"
      shift 2
      ;;
    --require-full)
      REQUIRE_FULL=1
      shift
      ;;
    --json)
      [[ $# -ge 2 ]] || { echo "error: --json needs a path" >&2; exit 2; }
      JSON_OUT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ "$TIER" != "full" ]]; then
  echo "error: Phase 1 supports only --tier full" >&2
  exit 2
fi

[[ -f "$MANIFEST" ]] || { echo "error: missing $MANIFEST" >&2; exit 1; }
[[ -f "$INVENTORY" ]] || { echo "error: missing $INVENTORY" >&2; exit 1; }
[[ -f "$TRUST_BASE" ]] || { echo "error: missing $TRUST_BASE" >&2; exit 1; }
command -v lake >/dev/null 2>&1 || { echo "error: lake is not available on PATH" >&2; exit 1; }

mkdir -p "$LOG_DIR"
RUN_DIR="$LOG_DIR/run-$$"
mkdir -p "$RUN_DIR"

INVENTORY_TSV="$RUN_DIR/inventory.tsv"
MANIFEST_TSV="$RUN_DIR/manifest.tsv"
REQUIRED_LABELS="$RUN_DIR/required_labels.txt"
INVENTORY_LABELS="$RUN_DIR/inventory_labels.txt"
MANIFEST_LABELS="$RUN_DIR/manifest_labels.txt"
PLACEHOLDER_LOG="$RUN_DIR/placeholders.log"
SEMANTIC_LOG="$RUN_DIR/semantic-audit.log"

json_escape() {
  local s="$1"
  s="${s//\\/\\\\}"
  s="${s//\"/\\\"}"
  s="${s//$'\n'/\\n}"
  s="${s//$'\r'/}"
  printf '%s' "$s"
}

parse_inventory() {
  awk '
    function trim(s) { gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    function unquote(s) {
      s = trim(s)
      if (s ~ /^".*"$/) { sub(/^"/, "", s); sub(/"$/, "", s) }
      return s
    }
    function emit() {
      if (entry_type == "" || paper_label == "") return
      if (required == "") required = "true"
      print entry_type "\t" paper_label "\t" required "\t" duplicate_of
    }
    /^\[\[definition\]\]/ {
      emit()
      entry_type = "definition"; paper_label = ""; required = ""; duplicate_of = ""
      next
    }
    /^\[\[claim\]\]/ {
      emit()
      entry_type = "claim"; paper_label = ""; required = ""; duplicate_of = ""
      next
    }
    /^[A-Za-z_]+[ \t]*=/ {
      key = $0
      sub(/[ \t]*=.*/, "", key)
      val = $0
      sub(/^[^=]*=/, "", val)
      val = unquote(val)
      if (key == "paper_label") paper_label = val
      else if (key == "required") required = val
      else if (key == "duplicate_of") duplicate_of = val
    }
    END { emit() }
  ' "$INVENTORY"
}

parse_manifest() {
  awk '
    function trim(s) { gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    function unquote(s) {
      s = trim(s)
      if (s ~ /^".*"$/) { sub(/^"/, "", s); sub(/"$/, "", s) }
      return s
    }
    function emit() {
      if (entry_type == "" || paper_label == "") return
      if (kind == "") kind = entry_type
      print entry_type "\t" paper_label "\t" kind "\t" status "\t" lean_subproject "\t" lean_module "\t" lean_decl
    }
    /^\[\[definition\]\]/ {
      emit()
      entry_type = "definition"; paper_label = ""; kind = "definition"; status = ""; lean_subproject = ""; lean_module = ""; lean_decl = ""
      next
    }
    /^\[\[claim\]\]/ {
      emit()
      entry_type = "claim"; paper_label = ""; kind = ""; status = ""; lean_subproject = ""; lean_module = ""; lean_decl = ""
      next
    }
    /^[A-Za-z_]+[ \t]*=/ {
      key = $0
      sub(/[ \t]*=.*/, "", key)
      val = $0
      sub(/^[^=]*=/, "", val)
      val = unquote(val)
      if (key == "paper_label") paper_label = val
      else if (key == "kind") kind = val
      else if (key == "status") status = val
      else if (key == "lean_subproject") lean_subproject = val
      else if (key == "lean_module") lean_module = val
      else if (key == "lean_decl") lean_decl = val
    }
    END { emit() }
  ' "$MANIFEST"
}

resolve_project() {
  local subproject="$1"
  if [[ "$subproject" == "." ]]; then
    printf '%s' "$ROOT/lean/full"
  else
    printf '%s' "$ROOT/lean/full/$subproject"
  fi
}

validate_decl_kind() {
  local project="$1" module="$2" decl="$3" log="$4"
  local probe_file="${log%.log}.lean"
  {
    printf 'import Lean\n'
    printf 'import %s\n\n' "$module"
    printf 'open Lean Elab Command\n\n'
    cat <<'LEAN'
elab "#validate_decl_kind " ident:ident : command => do
  let env <- getEnv
  let name := ident.getId
  match env.find? name with
  | none => logInfo "VALIDATE_DECL_KIND missing"
  | some (.axiomInfo _) => logInfo "VALIDATE_DECL_KIND axiom"
  | some (.thmInfo _) => logInfo "VALIDATE_DECL_KIND theorem"
  | some (.opaqueInfo _) => logInfo "VALIDATE_DECL_KIND opaque"
  | some (.defnInfo _) => logInfo "VALIDATE_DECL_KIND def"
  | some (.inductInfo _) => logInfo "VALIDATE_DECL_KIND inductive"
  | some (.ctorInfo _) => logInfo "VALIDATE_DECL_KIND constructor"
  | some (.recInfo _) => logInfo "VALIDATE_DECL_KIND recursor"
  | some (.quotInfo _) => logInfo "VALIDATE_DECL_KIND quotient"

LEAN
    printf '#validate_decl_kind %s\n' "$decl"
  } > "$probe_file"

  if ! (cd "$project" && lake env lean "$probe_file") >"$log" 2>&1; then
    printf 'unknown'
    return 1
  fi

  local kind
  kind="$(sed -n 's/.*VALIDATE_DECL_KIND //p' "$log" | tail -1 | tr -d '\r')"
  [[ -n "$kind" ]] || kind="unknown"
  printf '%s' "$kind"
}

audit_axioms() {
  local project="$1" module="$2" decl="$3" log="$4" axiom_list_out="$5"
  local probe_file="${log%.log}.lean"
  {
    printf 'import %s\n' "$module"
    printf '#print axioms %s\n' "$decl"
  } > "$probe_file"

  : > "$axiom_list_out"
  if ! (cd "$project" && lake env lean "$probe_file") >"$log" 2>&1; then
    return 1
  fi

  awk '
    /depends on axioms:/ {
      sub(/^.*depends on axioms:[[:space:]]*/, "")
      gsub(/[\[\],]/, " ")
      for (i = 1; i <= NF; i++) print $i
    }
  ' "$log" | sed '/^$/d' | sort -u > "$axiom_list_out"
}

is_trusted_axiom() {
  local axiom="$1"
  rg -qx --fixed-strings "$axiom" "$TRUST_BASE"
}

parse_inventory > "$INVENTORY_TSV"
parse_manifest > "$MANIFEST_TSV"

awk -F '\t' '$3 != "false" { print $2 }' "$INVENTORY_TSV" | sort -u > "$REQUIRED_LABELS"
awk -F '\t' '{ print $2 }' "$INVENTORY_TSV" | sort -u > "$INVENTORY_LABELS"
awk -F '\t' '{ print $2 }' "$MANIFEST_TSV" | sort -u > "$MANIFEST_LABELS"

inventory_fail=0
missing_labels="$(comm -23 "$REQUIRED_LABELS" "$MANIFEST_LABELS" || true)"
stale_labels="$(comm -23 "$MANIFEST_LABELS" "$INVENTORY_LABELS" || true)"

if [[ -n "$missing_labels" ]]; then
  echo "Missing manifest entries:" >&2
  echo "$missing_labels" >&2
  inventory_fail=1
fi

if [[ -n "$stale_labels" ]]; then
  echo "Stale manifest entries:" >&2
  echo "$stale_labels" >&2
  inventory_fail=1
fi

PROJECT="$ROOT/lean/full"
BUILD_STATUS="PASS"
build_fail=0
build_log="$RUN_DIR/build_full.log"

if [[ ! -f "$PROJECT/lean-toolchain" ]]; then
  echo "Missing lean-toolchain: lean/full" | tee "$build_log" >&2
  BUILD_STATUS="FAIL"
  build_fail=1
else
  toolchain="$(tr -d '\r\n' < "$PROJECT/lean-toolchain")"
  if [[ "$toolchain" != "$EXPECTED_TOOLCHAIN" ]]; then
    echo "Toolchain mismatch in lean/full: expected $EXPECTED_TOOLCHAIN, got $toolchain" | tee "$build_log" >&2
    BUILD_STATUS="FAIL"
    build_fail=1
  elif ! (cd "$PROJECT" && lake build) >"$build_log" 2>&1; then
    echo "Build failed: lean/full (see $build_log)" >&2
    BUILD_STATUS="FAIL"
    build_fail=1
  fi
fi

: > "$PLACEHOLDER_LOG"
placeholder_scan_fail=0
while IFS= read -r lean_file; do
  if rg -n '\b(sorry|admit)\b|by[[:space:]]+(aesop|simp|exact|rw|apply)\?' "$lean_file" >> "$PLACEHOLDER_LOG"; then
    placeholder_scan_fail=1
  fi
done < <(find "$PROJECT" -path '*/.lake' -prune -o -name '*.lean' -type f -print)

placeholder_count=0
if [[ -s "$PLACEHOLDER_LOG" ]]; then
  placeholder_count="$(wc -l < "$PLACEHOLDER_LOG" | tr -d ' ')"
fi

: > "$SEMANTIC_LOG"
semantic_audit_fail=0
while IFS= read -r lean_file; do
  {
    rg -n '^[[:space:]]*(def|abbrev)[[:space:]]+[A-Za-z0-9_.'\'']+.*:=[[:space:]]*(True|False)\b' "$lean_file" || true
    rg -n '^[[:space:]]*def[[:space:]]+WellFormed[A-Za-z0-9_.'\'']*.*:=[[:space:]]*True\b' "$lean_file" || true
    rg -n 'classify[A-Za-z0-9_.'\'']*[[:space:]]*:=[[:space:]]*fun[[:space:]]+_[[:space:]]*=>' "$lean_file" || true
  } | sed "s|^|$lean_file:|" >> "$SEMANTIC_LOG"
done < <(find "$PROJECT" -path '*/.lake' -prune -o -name '*.lean' -type f -print)

semantic_count=0
if [[ -s "$SEMANTIC_LOG" ]]; then
  semantic_count="$(wc -l < "$SEMANTIC_LOG" | tr -d ' ')"
  semantic_audit_fail=1
fi

probe_fail=0
probe_total=0
probe_pass=0
kind_fail=0
kind_total=0
kind_pass=0
axiom_fail=0
axiom_total=0
axiom_pass=0
declare -a ENTRY_JSON=()

printf '%-42s %-14s %-14s %-7s %-7s %-7s %-7s\n' "PAPER LABEL" "KIND" "STATUS" "BUILD" "PROBE" "DECL" "AXIOMS"

while IFS=$'\t' read -r entry_type paper_label kind status lean_subproject lean_module lean_decl; do
  [[ -n "$paper_label" ]] || continue
  build="$BUILD_STATUS"
  probe="--"
  kind_status="--"
  axiom_status="--"
  decl_kind=""
  axiom_list=""

  if [[ "$status" != "unformalized" ]]; then
    if [[ -z "$lean_subproject" || -z "$lean_module" || -z "$lean_decl" ]]; then
      probe_total=$((probe_total + 1))
      probe="FAIL"
      probe_fail=1
    else
      project="$(resolve_project "$lean_subproject")"
      if [[ ! -d "$project" ]]; then
        probe_total=$((probe_total + 1))
        probe="FAIL"
        probe_fail=1
      else
        probe_total=$((probe_total + 1))
        probe_file="$RUN_DIR/probe_${paper_label//[:\/]/_}.lean"
        probe_log="$RUN_DIR/probe_${paper_label//[:\/]/_}.log"
        {
          printf 'import %s\n' "$lean_module"
          printf '#check %s\n' "$lean_decl"
        } > "$probe_file"
        if (cd "$project" && lake env lean "$probe_file") >"$probe_log" 2>&1; then
          probe="PASS"
          probe_pass=$((probe_pass + 1))
        else
          probe="FAIL"
          probe_fail=1
        fi

        kind_total=$((kind_total + 1))
        kind_log="$RUN_DIR/kind_${paper_label//[:\/]/_}.log"
        if decl_kind="$(validate_decl_kind "$project" "$lean_module" "$lean_decl" "$kind_log")"; then
          case "$status:$decl_kind" in
            definition:def|definition:opaque|definition:inductive|definition:quotient|definition:constructor|definition:recursor)
              kind_status="PASS"
              ;;
            theorem:theorem)
              kind_status="PASS"
              ;;
            axiomatic:axiom|axiomatic:theorem|partial:theorem|partial:def|partial:inductive)
              kind_status="PASS"
              ;;
            *)
              kind_status="FAIL"
              kind_fail=1
              ;;
          esac
        else
          kind_status="FAIL"
          kind_fail=1
        fi
        [[ "$kind_status" == "PASS" ]] && kind_pass=$((kind_pass + 1))

        if [[ "$status" == "theorem" ]]; then
          axiom_total=$((axiom_total + 1))
          axiom_log="$RUN_DIR/axioms_${paper_label//[:\/]/_}.log"
          axiom_file="$RUN_DIR/axioms_${paper_label//[:\/]/_}.txt"
          if audit_axioms "$project" "$lean_module" "$lean_decl" "$axiom_log" "$axiom_file"; then
            bad_axiom=0
            while IFS= read -r axiom_name; do
              [[ -n "$axiom_name" ]] || continue
              if [[ -n "$axiom_list" ]]; then
                axiom_list="$axiom_list,$axiom_name"
              else
                axiom_list="$axiom_name"
              fi
              if ! is_trusted_axiom "$axiom_name"; then
                bad_axiom=1
              fi
            done < "$axiom_file"
            if [[ "$bad_axiom" -eq 0 ]]; then
              axiom_status="PASS"
              axiom_pass=$((axiom_pass + 1))
            else
              axiom_status="FAIL"
              axiom_fail=1
            fi
          else
            axiom_status="FAIL"
            axiom_fail=1
          fi
        fi
      fi
    fi
  fi

  printf '%-42s %-14s %-14s %-7s %-7s %-7s %-7s\n' "$paper_label" "$kind" "$status" "$build" "$probe" "$kind_status" "$axiom_status"
  ENTRY_JSON+=("$(printf '{"paper_label":"%s","kind":"%s","status":"%s","lean_module":"%s","lean_decl":"%s","build":"%s","probe":"%s","declaration_kind":"%s","kind_check":"%s","axiom_check":"%s","axioms":"%s"}' \
    "$(json_escape "$paper_label")" \
    "$(json_escape "$kind")" \
    "$(json_escape "$status")" \
    "$(json_escape "$lean_module")" \
    "$(json_escape "$lean_decl")" \
    "$(json_escape "$build")" \
    "$(json_escape "$probe")" \
    "$(json_escape "$decl_kind")" \
    "$(json_escape "$kind_status")" \
    "$(json_escape "$axiom_status")" \
    "$(json_escape "$axiom_list")")")
done < "$MANIFEST_TSV"

definitions_total="$(awk -F '\t' '$1 == "definition" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
claims_total="$(awk -F '\t' '$1 == "claim" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
definition_full="$(awk -F '\t' '$1 == "definition" && $4 == "definition" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
definition_unformalized="$(awk -F '\t' '$1 == "definition" && $4 == "unformalized" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
claim_theorem="$(awk -F '\t' '$1 == "claim" && $4 == "theorem" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
claim_unformalized="$(awk -F '\t' '$1 == "claim" && $4 == "unformalized" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"

strict_fail=0
if [[ "$REQUIRE_FULL" -eq 1 ]]; then
  non_full_defs="$(awk -F '\t' '$1 == "definition" && $4 != "definition" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
  non_full_claims="$(awk -F '\t' '$1 == "claim" && $4 != "theorem" { c++ } END { print c + 0 }' "$MANIFEST_TSV")"
  if [[ "$non_full_defs" -gt 0 || "$non_full_claims" -gt 0 ]]; then
    strict_fail=1
  fi
fi

echo
echo "Summary: $definitions_total definitions, $claims_total required claims"
echo "Definitions: full $definition_full, unformalized $definition_unformalized"
echo "Claims: theorem $claim_theorem, unformalized $claim_unformalized"
echo "Builds: $([[ "$build_fail" -eq 0 ]] && echo "1/1 passing" || echo "0/1 passing")"
echo "Probes: $probe_pass/$probe_total passing"
echo "Declaration kinds: $kind_pass/$kind_total passing"
echo "Axiom audits: $axiom_pass/$axiom_total passing"
echo "Placeholders: $placeholder_count found"
echo "Semantic audit: $semantic_count findings"

validation_fail=0
if [[ "$inventory_fail" -ne 0 || "$build_fail" -ne 0 || "$probe_fail" -ne 0 || "$kind_fail" -ne 0 || "$axiom_fail" -ne 0 || "$placeholder_scan_fail" -ne 0 || "$semantic_audit_fail" -ne 0 ]]; then
  validation_fail=1
fi

final_status="partial_pass"
if [[ "$validation_fail" -ne 0 ]]; then
  final_status="validation_fail"
elif [[ "$REQUIRE_FULL" -eq 1 && "$strict_fail" -ne 0 ]]; then
  final_status="full_fail"
elif [[ "$REQUIRE_FULL" -eq 1 ]]; then
  final_status="full_pass"
fi

if [[ -n "$JSON_OUT" ]]; then
  mkdir -p "$(dirname "$JSON_OUT")"
  {
    printf '{\n'
    printf '  "final_status": "%s",\n' "$final_status"
    printf '  "definitions": {"total": %s, "full": %s, "unformalized": %s},\n' "$definitions_total" "$definition_full" "$definition_unformalized"
    printf '  "claims": {"total": %s, "theorem": %s, "unformalized": %s},\n' "$claims_total" "$claim_theorem" "$claim_unformalized"
    printf '  "builds": {"total": 1, "passing": %s, "failing": %s},\n' "$((1 - build_fail))" "$build_fail"
    printf '  "probes": {"total": %s, "passing": %s, "failing": %s},\n' "$probe_total" "$probe_pass" "$((probe_total - probe_pass))"
    printf '  "declaration_kinds": {"total": %s, "passing": %s, "failing": %s},\n' "$kind_total" "$kind_pass" "$((kind_total - kind_pass))"
    printf '  "axiom_audits": {"total": %s, "passing": %s, "failing": %s},\n' "$axiom_total" "$axiom_pass" "$((axiom_total - axiom_pass))"
    printf '  "semantic_audit": {"findings": %s, "passing": %s},\n' "$semantic_count" "$([[ "$semantic_audit_fail" -eq 0 ]] && echo true || echo false)"
    printf '  "placeholders": {"count": %s, "passing": %s},\n' "$placeholder_count" "$([[ "$placeholder_scan_fail" -eq 0 ]] && echo true || echo false)"
    printf '  "require_full": %s,\n' "$REQUIRE_FULL"
    printf '  "strict_pass": %s,\n' "$([[ "$strict_fail" -eq 0 && "$validation_fail" -eq 0 ]] && echo true || echo false)"
    printf '  "entries": [\n'
    for i in "${!ENTRY_JSON[@]}"; do
      if [[ "$i" -gt 0 ]]; then
        printf ',\n'
      fi
      printf '    %s' "${ENTRY_JSON[$i]}"
    done
    printf '\n  ]\n'
    printf '}\n'
  } > "$JSON_OUT"
fi

if [[ "$validation_fail" -ne 0 ]]; then
  echo "Overall: VALIDATION FAIL" >&2
  [[ "$placeholder_scan_fail" -ne 0 ]] && echo "Reason: unresolved proof placeholders found; see $PLACEHOLDER_LOG" >&2
  [[ "$semantic_audit_fail" -ne 0 ]] && echo "Reason: semantic audit findings found; see $SEMANTIC_LOG" >&2
  exit 1
fi

if [[ "$REQUIRE_FULL" -eq 1 && "$strict_fail" -ne 0 ]]; then
  echo "Overall: FULL MECHANIZATION FAIL" >&2
  echo "Reason: unformalized, partial, or axiomatic manifest entries remain." >&2
  exit 1
fi

if [[ "$REQUIRE_FULL" -eq 1 ]]; then
  echo "Overall: FULL MECHANIZATION PASS"
else
  echo "Overall: PARTIAL PASS"
fi
