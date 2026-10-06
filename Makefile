LATEXMK = latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build

FOUNDATIONS_IV_DIR = paper/foundations_iv
META_MATH_DIR = paper/meta_math

PAPER_AUX_EXTS = aux log bbl blg toc out synctex.gz fdb_latexmk fls

# PREP_SKELETON_MODE=1 suppresses the single known prep-state warning
# (Overfull \vbox caused by empty skeleton sections); this is the
# escape hatch for running the gate before the first body dispatch
# lands. Set to empty (default) for the strict drafting-time gate.
PREP_SKELETON_MODE ?=

.PHONY: help \
	paper-build-foundations_iv paper-build-meta_math paper-build \
	paper-preflight-foundations_iv paper-preflight-meta_math paper-preflight \
	paper-clean-foundations_iv paper-clean-meta_math paper-clean

.NOTPARALLEL:

help:
	@echo "Available targets:"
	@echo "  paper-build-foundations_iv     Build Foundations IV PDF at $(FOUNDATIONS_IV_DIR)/build/main.pdf"
	@echo "  paper-build-meta_math          Build Meta-math PDF at $(META_MATH_DIR)/build/main.pdf"
	@echo "  paper-build                    Build all paper PDFs"
	@echo "  paper-preflight-foundations_iv Build, lint, and log-check Foundations IV"
	@echo "  paper-preflight-meta_math      Build, lint, and log-check Meta-math"
	@echo "  paper-preflight                Preflight all papers and run registry validators"
	@echo "  paper-clean-foundations_iv     Remove Foundations IV build artifacts"
	@echo "  paper-clean-meta_math          Remove Meta-math build artifacts"
	@echo "  paper-clean                    Remove build artifacts for all papers"
	@echo "  help                           Show this target list"

# ----- build targets -----

paper-build-foundations_iv:
	cd $(FOUNDATIONS_IV_DIR) && BIBINPUTS=..: $(LATEXMK) main.tex

paper-build-meta_math:
	@test -f $(META_MATH_DIR)/main.tex || { echo "skip: $(META_MATH_DIR)/main.tex not present yet"; exit 0; }
	cd $(META_MATH_DIR) && BIBINPUTS=..: $(LATEXMK) main.tex

paper-build: paper-build-foundations_iv paper-build-meta_math

# ----- preflight targets -----

paper-preflight-foundations_iv: paper-build-foundations_iv
	scripts/paper_lint.sh $(FOUNDATIONS_IV_DIR)
	@log="$(FOUNDATIONS_IV_DIR)/build/main.log"; \
	test -f "$$log" || { echo "error: missing build log $$log"; exit 1; }; \
	pattern='Underfull|Overfull|Float too large|undefined references|undefined citations|Reference .* undefined|Citation .* undefined|There were undefined|Cref Cref|\\\\Cref.*\\\\Cref'; \
	if [ -n "$(PREP_SKELETON_MODE)" ]; then \
	  echo "info: PREP_SKELETON_MODE=1 — suppressing known empty-skeleton Overfull \\vbox warning"; \
	  hits=$$(grep -nE "$$pattern" "$$log" | grep -vF 'Overfull \vbox' | grep -v 'while \\output is active' || true); \
	else \
	  hits=$$(grep -nE "$$pattern" "$$log" || true); \
	fi; \
	if [ -n "$$hits" ]; then \
	  echo "$$hits"; \
	  echo "error: Foundations IV build log contains layout/reference warnings"; \
	  exit 1; \
	fi
	python3 scripts/check_statements_of_record_foundations_iv.py

paper-preflight-meta_math:
	@test -f $(META_MATH_DIR)/main.tex || { echo "skip: meta_math not yet in drafting"; exit 0; }
	$(MAKE) paper-build-meta_math
	scripts/paper_lint.sh $(META_MATH_DIR)
	@log="$(META_MATH_DIR)/build/main.log"; \
	test -f "$$log" || { echo "error: missing build log $$log"; exit 1; }; \
	if grep -nE 'Underfull|Overfull|Float too large|undefined references|undefined citations|Reference .* undefined|Citation .* undefined|There were undefined|Cref Cref|\\\\Cref.*\\\\Cref' "$$log"; then \
	  echo "error: Meta-math build log contains layout/reference warnings"; \
	  exit 1; \
	fi
	python3 scripts/check_statements_of_record_meta_math.py

paper-preflight: paper-preflight-foundations_iv paper-preflight-meta_math
	python3 scripts/check_manifests.py --check

# ----- clean targets -----

paper-clean-foundations_iv:
	rm -rf $(FOUNDATIONS_IV_DIR)/build
	@for ext in $(PAPER_AUX_EXTS); do rm -f "$(FOUNDATIONS_IV_DIR)"/*.$$ext; done

paper-clean-meta_math:
	rm -rf $(META_MATH_DIR)/build
	@for ext in $(PAPER_AUX_EXTS); do rm -f "$(META_MATH_DIR)"/*.$$ext; done

paper-clean: paper-clean-foundations_iv paper-clean-meta_math
