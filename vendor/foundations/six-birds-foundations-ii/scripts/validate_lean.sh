#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/lean/manifest.toml"
LOG_DIR="$ROOT/lean/.validate-logs"
TRUST_BASE="$ROOT/lean/trust_base.txt"
EXPECTED_TOOLCHAIN="leanprover/lean4:v4.28.0"

TIER="recovered"
TIER_SET=0
REQUIRE_FULL=0
DOWNLOAD_MATHLIB=0
JSON_OUT=""

usage() {
  cat <<'USAGE'
Usage: scripts/validate_lean.sh [--tier recovered|full] [--require-full] [--download-mathlib] [--json PATH]

Default mode validates the recovered partial Lean track. --require-full keeps all checks
but fails unless every paper definition and theorem/proposition claim is fully formalized.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --tier)
      [[ $# -ge 2 ]] || { echo "error: --tier needs a value" >&2; exit 2; }
      TIER="$2"
      TIER_SET=1
      shift 2
      ;;
    --require-full)
      REQUIRE_FULL=1
      shift
      ;;
    --download-mathlib)
      DOWNLOAD_MATHLIB=1
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

if [[ "$REQUIRE_FULL" -eq 1 && "$TIER_SET" -eq 0 && -d "$ROOT/lean/full" ]]; then
  TIER="full"
fi

if [[ "$TIER" != "recovered" && "$TIER" != "full" ]]; then
  echo "error: --tier must be 'recovered' or 'full'" >&2
  exit 2
fi

mkdir -p "$LOG_DIR"
RUN_DIR="$LOG_DIR/run-$$"
mkdir -p "$RUN_DIR"
ENTRIES_TSV="$RUN_DIR/manifest_entries.tsv"
EXPECTED_DEFS="$RUN_DIR/expected_definitions.txt"
EXPECTED_CLAIMS="$RUN_DIR/expected_claims.txt"
MANIFEST_DEFS="$RUN_DIR/manifest_definitions.txt"
MANIFEST_CLAIMS="$RUN_DIR/manifest_claims.txt"

project_rel() {
  local project="$1"
  if [[ "$project" == "$ROOT/lean/recovered/"* ]]; then
    printf '%s' "${project#$ROOT/lean/recovered/}"
  elif [[ "$project" == "$ROOT/lean/full" ]]; then
    printf '.'
  elif [[ "$project" == "$ROOT/lean/full/"* ]]; then
    printf '%s' "${project#$ROOT/lean/full/}"
  else
    printf '%s' "$project"
  fi
}

uses_mathlib() {
  local project="$1"
  [[ -f "$project/lakefile.toml" ]] && rg -q 'name[[:space:]]*=[[:space:]]*"mathlib"' "$project/lakefile.toml"
}

resolve_manifest_project() {
  local subproject="$1"
  if [[ "$subproject" == "." && -f "$ROOT/lean/full/lakefile.toml" ]]; then
    printf '%s' "$ROOT/lean/full"
    return 0
  fi
  if [[ "$TIER" == "full" && -d "$ROOT/lean/full/$subproject" ]]; then
    printf '%s' "$ROOT/lean/full/$subproject"
    return 0
  fi
  if [[ -d "$ROOT/lean/recovered/$subproject" ]]; then
    printf '%s' "$ROOT/lean/recovered/$subproject"
    return 0
  fi
  if [[ -d "$ROOT/lean/full/$subproject" ]]; then
    printf '%s' "$ROOT/lean/full/$subproject"
    return 0
  fi
  return 1
}

if [[ ! -f "$MANIFEST" ]]; then
  echo "error: missing $MANIFEST" >&2
  exit 1
fi

if [[ ! -f "$TRUST_BASE" ]]; then
  echo "error: missing $TRUST_BASE" >&2
  exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake is not available on PATH" >&2
  exit 1
fi

parse_manifest() {
  awk '
    function trim(s) { gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    function unquote(s) {
      s = trim(s)
      if (s ~ /^".*"$/) { sub(/^"/, "", s); sub(/"$/, "", s) }
      return s
    }
    function emit() {
      if (entry_type == "") return
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

extract_expected_inventory() {
  rg -o '\\begin\{definition\}.*\\label\{[^}]+\}' "$ROOT/paper/sections" \
    | sed -E 's/.*\\label\{([^}]+)\}.*/\1/' \
    | sort -u > "$EXPECTED_DEFS"

  {
    rg -o '\\begin\{theorem\}.*\\label\{[^}]+\}' "$ROOT/paper/sections" || true
    rg -o '\\begin\{proposition\}.*\\label\{[^}]+\}' "$ROOT/paper/sections" || true
  } | sed -E 's/.*\\label\{([^}]+)\}.*/\1/' \
    | sort -u > "$EXPECTED_CLAIMS"
}

json_escape() {
  local s="$1"
  s="${s//\\/\\\\}"
  s="${s//\"/\\\"}"
  s="${s//$'\n'/\\n}"
  s="${s//$'\r'/}"
  printf '%s' "$s"
}

status_json_bool() {
  [[ "$1" == "PASS" ]] && printf true || printf false
}

is_trusted_axiom() {
  local axiom="$1"
  rg -qx --fixed-strings "$axiom" "$TRUST_BASE"
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

  sed -n "s/.*'%s' depends on axioms: //p" "$log" >/dev/null 2>&1 || true
  awk '
    /depends on axioms:/ {
      sub(/^.*depends on axioms:[[:space:]]*/, "")
      gsub(/[\[\],]/, " ")
      for (i = 1; i <= NF; i++) print $i
    }
    /does not depend on any axioms/ { found_none = 1 }
  ' "$log" | sed '/^$/d' | sort -u > "$axiom_list_out"
}

placeholder_scan_fail=0
placeholder_count=0
PLACEHOLDER_LOG="$RUN_DIR/placeholders.log"
: > "$PLACEHOLDER_LOG"

semantic_audit_fail=0
semantic_audit_count=0
SEMANTIC_AUDIT_LOG="$RUN_DIR/semantic-audit.log"
: > "$SEMANTIC_AUDIT_LOG"

parse_manifest > "$ENTRIES_TSV"
extract_expected_inventory

awk -F '\t' '$1 == "definition" { print $2 }' "$ENTRIES_TSV" | sort -u > "$MANIFEST_DEFS"
awk -F '\t' '$1 == "claim" { print $2 }' "$ENTRIES_TSV" | sort -u > "$MANIFEST_CLAIMS"

inventory_fail=0
missing_defs="$(comm -23 "$EXPECTED_DEFS" "$MANIFEST_DEFS" || true)"
missing_claims="$(comm -23 "$EXPECTED_CLAIMS" "$MANIFEST_CLAIMS" || true)"
stale_defs="$(comm -13 "$EXPECTED_DEFS" "$MANIFEST_DEFS" || true)"
stale_claims="$(comm -13 "$EXPECTED_CLAIMS" "$MANIFEST_CLAIMS" || true)"

if [[ -n "$missing_defs" ]]; then
  echo "Missing definition manifest entries:" >&2
  echo "$missing_defs" >&2
  inventory_fail=1
fi
if [[ -n "$missing_claims" ]]; then
  echo "Missing claim manifest entries:" >&2
  echo "$missing_claims" >&2
  inventory_fail=1
fi
if [[ -n "$stale_defs" ]]; then
  echo "Stale definition manifest entries:" >&2
  echo "$stale_defs" >&2
  inventory_fail=1
fi
if [[ -n "$stale_claims" ]]; then
  echo "Stale claim manifest entries:" >&2
  echo "$stale_claims" >&2
  inventory_fail=1
fi

declare -a PROJECTS=()
if [[ "$TIER" == "recovered" ]]; then
  while IFS= read -r project; do
    PROJECTS+=("$project")
  done < <(find "$ROOT/lean/recovered/substantive" "$ROOT/lean/recovered/skeletons" -mindepth 1 -maxdepth 1 -type d | sort)
else
  if [[ -d "$ROOT/lean/full" ]]; then
    while IFS= read -r lakefile; do
      PROJECTS+=("$(dirname "$lakefile")")
    done < <(find "$ROOT/lean/full" -name lakefile.toml -type f | sort)
  fi
fi

for project in "${PROJECTS[@]}"; do
  while IFS= read -r lean_file; do
    if rg -n '\b(sorry|admit)\b|by[[:space:]]+(aesop|simp|exact|rw|apply)\?' "$lean_file" >> "$PLACEHOLDER_LOG"; then
      placeholder_scan_fail=1
    fi
  done < <(find "$project" -path '*/.lake' -prune -o -name '*.lean' -type f -print)
done
if [[ -s "$PLACEHOLDER_LOG" ]]; then
  placeholder_count="$(wc -l < "$PLACEHOLDER_LOG" | tr -d ' ')"
else
  placeholder_count=0
fi

if [[ "$REQUIRE_FULL" -eq 1 && "$TIER" == "full" ]]; then
  while IFS= read -r lean_file; do
    {
      rg -n '^[[:space:]]*(def|abbrev)[[:space:]]+[A-Za-z0-9_.'\'']+.*:=[[:space:]]*(True|False)\b' "$lean_file" || true
      rg -n '^[[:space:]]*def[[:space:]]+WellFormed[A-Za-z0-9_.'\'']*.*:=[[:space:]]*True\b' "$lean_file" || true
      rg -n '^[[:space:]]*def[[:space:]]+[A-Za-z0-9_.'\'']*Classified[A-Za-z0-9_.'\'']*.*:=[[:space:]]*∃[[:space:]]+c[[:space:]]*:[[:space:]]*ResidualClass,[[:space:]]*CoveredResidualClass[[:space:]]+c' "$lean_file" || true
      rg -n 'classify[[:space:]]*:=[[:space:]]*fun[[:space:]]+_[[:space:]]*=>[[:space:]]*ResidualClass\.outsideDomainStructure' "$lean_file" || true
    } | sed "s|^|$lean_file:|" >> "$SEMANTIC_AUDIT_LOG"
  done < <(find "$ROOT/lean/full" -path '*/.lake' -prune -o -name '*.lean' -type f -print)

  if [[ -s "$SEMANTIC_AUDIT_LOG" ]]; then
    semantic_audit_count="$(wc -l < "$SEMANTIC_AUDIT_LOG" | tr -d ' ')"
    semantic_audit_fail=1
  fi
fi

build_fail=0
declare -A BUILD_STATUS

for project in "${PROJECTS[@]}"; do
  rel="$(project_rel "$project")"
  log_name="${rel//\//__}"
  log="$RUN_DIR/build_${log_name}.log"
  BUILD_STATUS["$rel"]="PASS"

  if [[ ! -f "$project/lean-toolchain" ]]; then
    echo "Missing lean-toolchain: $rel" | tee "$log" >&2
    BUILD_STATUS["$rel"]="FAIL"
    build_fail=1
    continue
  fi

  toolchain="$(tr -d '\r\n' < "$project/lean-toolchain")"
  if [[ "$toolchain" != "$EXPECTED_TOOLCHAIN" ]]; then
    echo "Toolchain mismatch in $rel: expected $EXPECTED_TOOLCHAIN, got $toolchain" | tee "$log" >&2
    BUILD_STATUS["$rel"]="FAIL"
    build_fail=1
    continue
  fi

  (
    cd "$project"
    echo "== $rel =="
    if uses_mathlib "$project" && [[ "$DOWNLOAD_MATHLIB" -eq 1 || ! -f ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]]; then
      lake exe cache get
    fi
    lake build
  ) >"$log" 2>&1 || {
    echo "Build failed: $rel (see $log)" >&2
    BUILD_STATUS["$rel"]="FAIL"
    build_fail=1
  }
done

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

printf '%-38s %-12s %-14s %-42s %-7s %-7s %-7s %-7s\n' "PAPER LABEL" "KIND" "STATUS" "LEAN SUBPROJECT" "BUILD" "PROBE" "DECL" "AXIOMS"

while IFS=$'\t' read -r entry_type paper_label kind status lean_subproject lean_module lean_decl; do
  [[ -n "$paper_label" ]] || continue
  build="--"
  probe="--"
  kind_status="--"
  axiom_status="--"
  semantic_status="--"
  decl_kind=""
  axiom_list=""

  if [[ "$status" != "unformalized" ]]; then
    if [[ -z "$lean_subproject" || -z "$lean_module" || -z "$lean_decl" ]]; then
      probe_total=$((probe_total + 1))
      probe="FAIL"
      probe_fail=1
    else
      project="$(resolve_manifest_project "$lean_subproject" || true)"
      build="${BUILD_STATUS[$lean_subproject]:---}"
      if [[ "$REQUIRE_FULL" -eq 0 && "$TIER" == "recovered" && "$project" == "$ROOT/lean/full"* ]]; then
        probe="SKIP"
        kind_status="SKIP"
        axiom_status="SKIP"
        semantic_status="SKIP"
      elif [[ ! -d "$project" ]]; then
        probe_total=$((probe_total + 1))
        probe="FAIL"
        probe_fail=1
      else
        probe_total=$((probe_total + 1))
        probe_file="$RUN_DIR/probe_${paper_label//:/_}.lean"
        probe_log="$RUN_DIR/probe_${paper_label//:/_}.log"
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
        kind_log="$RUN_DIR/kind_${paper_label//:/_}.log"
        if decl_kind="$(validate_decl_kind "$project" "$lean_module" "$lean_decl" "$kind_log")"; then
          case "$status:$decl_kind" in
            definition:def|definition:opaque|definition:inductive|definition:quotient|definition:constructor|definition:recursor)
              kind_status="PASS"
              ;;
            theorem:theorem|partial:theorem|partial:def|partial:opaque|partial:inductive|partial:quotient|partial:constructor|partial:recursor|axiomatic:axiom|axiomatic:theorem|axiomatic:def|axiomatic:opaque|axiomatic:inductive|axiomatic:quotient|axiomatic:constructor|axiomatic:recursor)
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
          axiom_log="$RUN_DIR/axioms_${paper_label//:/_}.log"
          axiom_file="$RUN_DIR/axioms_${paper_label//:/_}.txt"
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
        elif [[ "$status" == "axiomatic" ]]; then
          axiom_status="ALLOW"
        fi

        if [[ "$REQUIRE_FULL" -eq 1 && "$TIER" == "full" && "$project" == "$ROOT/lean/full"* ]]; then
          if [[ "$semantic_audit_fail" -eq 0 ]]; then
            semantic_status="PASS"
          else
            semantic_status="FAIL"
          fi
        fi
      fi
    fi
  fi

  printf '%-38s %-12s %-14s %-42s %-7s %-7s %-7s %-7s\n' "$paper_label" "$kind" "$status" "${lean_subproject:---}" "$build" "$probe" "$kind_status" "$axiom_status"
  ENTRY_JSON+=("$(printf '{"paper_label":"%s","kind":"%s","status":"%s","lean_subproject":"%s","lean_module":"%s","lean_decl":"%s","build":"%s","probe":"%s","declaration_kind":"%s","kind_check":"%s","axiom_check":"%s","semantic_check":"%s","axioms":"%s"}' \
    "$(json_escape "$paper_label")" \
    "$(json_escape "$kind")" \
    "$(json_escape "$status")" \
    "$(json_escape "$lean_subproject")" \
    "$(json_escape "$lean_module")" \
    "$(json_escape "$lean_decl")" \
    "$(json_escape "$build")" \
    "$(json_escape "$probe")" \
    "$(json_escape "$decl_kind")" \
    "$(json_escape "$kind_status")" \
    "$(json_escape "$axiom_status")" \
    "$(json_escape "$semantic_status")" \
    "$(json_escape "$axiom_list")")")
done < "$ENTRIES_TSV"

definitions_total="$(wc -l < "$EXPECTED_DEFS" | tr -d ' ')"
claims_total="$(wc -l < "$EXPECTED_CLAIMS" | tr -d ' ')"
definition_unformalized="$(awk -F '\t' '$1 == "definition" && $4 == "unformalized" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"
definition_formalized=$((definitions_total - definition_unformalized))
claim_theorem="$(awk -F '\t' '$1 == "claim" && $4 == "theorem" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"
claim_partial="$(awk -F '\t' '$1 == "claim" && $4 == "partial" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"
claim_axiomatic="$(awk -F '\t' '$1 == "claim" && $4 == "axiomatic" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"
claim_unformalized="$(awk -F '\t' '$1 == "claim" && $4 == "unformalized" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"

strict_fail=0
if [[ "$REQUIRE_FULL" -eq 1 ]]; then
  non_full_defs="$(awk -F '\t' '$1 == "definition" && $4 != "definition" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"
  non_full_claims="$(awk -F '\t' '$1 == "claim" && $4 != "theorem" { c++ } END { print c + 0 }' "$ENTRIES_TSV")"
  if [[ "$non_full_defs" -gt 0 || "$non_full_claims" -gt 0 ]]; then
    strict_fail=1
  fi
fi

echo
echo "Summary: $definitions_total definitions, $claims_total theorem/proposition claims"
echo "Definitions: formalized $definition_formalized, unformalized $definition_unformalized"
echo "Claims: theorem $claim_theorem, partial $claim_partial, axiomatic $claim_axiomatic, unformalized $claim_unformalized"
echo "Builds: $((${#PROJECTS[@]} - build_fail))/${#PROJECTS[@]} passing"
echo "Probes: $probe_pass/$probe_total passing"
echo "Declaration kinds: $kind_pass/$kind_total passing"
echo "Axiom audits: $axiom_pass/$axiom_total passing"
echo "Placeholders: $placeholder_count found"
echo "Semantic audit: $semantic_audit_count findings"

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
    printf '  "definitions": {"total": %s, "formalized": %s, "unformalized": %s},\n' "$definitions_total" "$definition_formalized" "$definition_unformalized"
    printf '  "claims": {"total": %s, "theorem": %s, "partial": %s, "axiomatic": %s, "unformalized": %s},\n' "$claims_total" "$claim_theorem" "$claim_partial" "$claim_axiomatic" "$claim_unformalized"
    printf '  "builds": {"total": %s, "passing": %s, "failing": %s},\n' "${#PROJECTS[@]}" "$((${#PROJECTS[@]} - build_fail))" "$build_fail"
    printf '  "probes": {"total": %s, "passing": %s, "failing": %s},\n' "$probe_total" "$probe_pass" "$((probe_total - probe_pass))"
    printf '  "declaration_kinds": {"total": %s, "passing": %s, "failing": %s},\n' "$kind_total" "$kind_pass" "$((kind_total - kind_pass))"
    printf '  "axiom_audits": {"total": %s, "passing": %s, "failing": %s},\n' "$axiom_total" "$axiom_pass" "$((axiom_total - axiom_pass))"
    printf '  "semantic_audit": {"findings": %s, "passing": %s},\n' "$semantic_audit_count" "$([[ "$semantic_audit_fail" -eq 0 ]] && echo true || echo false)"
    printf '  "placeholders": {"count": %s, "passing": %s},\n' "$placeholder_count" "$([[ "$placeholder_scan_fail" -eq 0 ]] && echo true || echo false)"
    printf '  "require_full": %s,\n' "$REQUIRE_FULL"
    printf '  "strict_pass": %s,\n' "$([[ "$strict_fail" -eq 0 && "$semantic_audit_fail" -eq 0 ]] && echo true || echo false)"
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
  echo "Overall: PARTIAL VALIDATION FAIL" >&2
  if [[ "$placeholder_scan_fail" -ne 0 ]]; then
    echo "Reason: unresolved proof placeholders found; see $PLACEHOLDER_LOG" >&2
  fi
  if [[ "$semantic_audit_fail" -ne 0 ]]; then
    echo "Reason: semantic audit findings found; see $SEMANTIC_AUDIT_LOG" >&2
  fi
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
