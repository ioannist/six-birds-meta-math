# Paper Proposal — Type-Finite Foreclosure and Recognition-Mode Landings

Historical proposal. The maintained manuscript is `main.tex`. Its current
claim status supersedes the proposal's earlier "landed" and "two-instance
verified" phrasing: T1--T10 include guarded obligations, the application
endpoints have distinct explicit premises, and the joint RH--Navier Gaussian
theorem is a separate checked result.

## Working title

**Type-Finite Foreclosure and Recognition-Mode Landings: A Meta-Theoretic Account of Clay-Class Closure in Six Birds Theory**

Alternatives:
- *Two Halves of One Meta-Thesis: Why Clay-Class Closures Land Where They Do in Six Birds*
- *Carrier Dichotomy and Recognition-Mode Landings: How the Six Birds Framework Closes (and Cannot Close) Clay-Class Problems*

## One-paragraph pitch

The Six Birds framework has now landed three Clay-class problems under standard Foundations I closure assumption — Navier–Stokes regularity (substrate-specific apparatus), P vs NP (recognition source `Γ_csl-sat-hidden`), and the Riemann Hypothesis (recognition source `Γ_SDTC^Selberg`). This paper extracts the meta-theoretic account of why those landings have the shape they do, in two complementary halves. **Negative half** (Carrier Dichotomy, Type-Finite Foreclosure, Attack Foreclosure v4): every framework-internal carrier attempt at a Clay-class conjecture `X` falls into one of four typed states — non-`X`-equivalent, CRE-TE, CRE-BF, or CRE-CTMT — and no chain of internal moves (carrier pivot, bridge import, cascade-internal computation) can close `X` without external classical content. **Positive half** (Recognition-Mode Landing Template, Attack Foreclosure v5): for substrates in V-Differential's trace-state-only column, a structurally distinct closure path exists — the seven-stage recognition-mode landing template — which lands at theorem-grade under SB closure assumption with a named structural source rather than a derived one. The two halves are joint: v5 *refines* v4 rather than refuting it. The paper documents the typed apparatus (carrier classification, CRCFT modes, CTMT recursion, calibration-family structure, functorial-gate species) used by both halves and validated cross-track on NS, RH, and P vs NP.

## Scope

**In**: the three landed Clay-class problems — Navier–Stokes regularity, P vs NP, Riemann Hypothesis. All theorems are scoped to evidence available on these three tracks plus framework-general apparatus.

**Out**:
- BSD and Hodge tracks (no landings yet; cross-track validation evidence from these tracks is not used here)
- Standalone proof of any Clay-class problem (those are the sibling papers — paper 5 NS, paper 6 RH, paper 7 PvNP)
- Standard-ZFC unconditional claims
- Cross-track signature beyond two-instance recognition-mode replication (PvNP, RH)

## Section outline

1. **Introduction.** The three Clay-class landings; why a meta-paper; relation to sibling papers 2/3/4/5/6/7/8.
2. **The adequacy calculus and the typed-context discipline.** Black-box from `adequacy.tex` (paper 1) and `needles.tex` (paper 4); the legal energy quotient; null-mode legality; the all-six taxonomy.
3. **Carrier Dichotomy and Type-Finite Foreclosure** (Part I — negative half).
   - 3.1 Carrier Dichotomy Theorem.
   - 3.2 Bridge Impossibility Corollary.
   - 3.3 Coverage Theorem (the four-state classification is exhaustive).
   - 3.4 Type-Finite Foreclosure: the door-space is type-finite.
   - 3.5 Attack Foreclosure (v4): no framework-internal chain closes `X`.
   - 3.6 CTMT recursion: multi-layer terminal cascades.
4. **The Recognition-Mode Landing Template** (Part II — positive half).
   - 4.1 V-Differential's substrate classification; the trace-state-only column.
   - 4.2 The seven-stage template: closure construction → translation theorem → applicability audit → smuggle audit → anti-tautology hardening → three-option derivation sweep → recognition closure under SB closure assumption.
   - 4.3 The `(ii)/(iii)/(ii)` verdict signature: structural account.
   - 4.4 Closure-content thesis: hiddenness / fixed-locus confinement is closure-content, not separately-derivable.
   - 4.5 Attack Foreclosure (v5 refinement): recognition-mode landings are a structurally distinct path; v4 stands for derivation routes.
5. **Cross-track validation on the three landed Clay-class problems.**
   - 5.1 Navier–Stokes (witness-content-exposing column): substrate-specific landing via `needles.tex` membrane endpoint + 9-record closure bundle. Provides the v4-style derivation-route control.
   - 5.2 P vs NP (trace-state-only column): recognition-mode landing via `Γ_csl-sat-hidden`. Stage-by-stage template instance with `(ii)/(iii)/(ii)` signature.
   - 5.3 Riemann Hypothesis (trace-state-only column): recognition-mode landing via `Γ_SDTC^Selberg`. Stage-by-stage template instance with `(ii)/(iii)/(ii)` signature.
   - 5.4 The cross-track signature.
6. **The Calibration Family** (Part III — framework-general apparatus, PvNP-derived).
   - 6.1 Calibration-Family Structure (Theorem 8): non-descending calibration as a typed family, not a single instrument.
   - 6.2 Calibration-Family Discipline (Theorem 8.1): rebadge detection and honest retract.
   - 6.3 Bridges-as-Theorems (Theorem 9) and Bridge Type-Direction (Theorem 9.1).
   - 6.4 Coverage-Family Geometry (Theorem 10): typed holes, not a category-theoretic colimit.
   - 6.5 Framework-Type Self-Characterization (Theorem 11): the cascade's natural object-type vs. Clay-target object-type.
   - 6.6 Named Functorial Gates (Theorem 12): a new typed-deposit species.
7. **Cross-paper consistency audit.** Source-record discipline across papers 2/6/7/8 and this paper; V-Differential placement consistency; recognition-closure architecture consistency.
8. **Predictions and open problems.**
   - 8.1 Generalization predictions for tracks not landed (Hodge, Yang-Mills) — explicitly speculative.
   - 8.2 Theorem-grade lifting of the `(ii)/(iii)/(ii)` signature (currently two-instance).
   - 8.3 Theorem-grade lifting of the closure-content thesis.
   - 8.4 Calibration-family extensions and the still-open functorial gates.
9. **Nonclaims and honest caveats.**

## Key theorems (consolidated)

From the foreclosure half:
- **T1 Carrier Dichotomy** — four typed states partition every framework-audited carrier aimed at `X`.
- **T2 Bridge Impossibility Corollary** — any bridge composing a non-`X`-equivalent carrier into `X`-closure inherits the `X`-strength obligation.
- **T3 Coverage Theorem** *(candidate — central proof obligation per M6 source; requires (i) precise definition of "open conjecture relative to accepted-imports base" and (ii) a relative-consistency argument `CRE + closure-from-base ⟹ X ∈ base`; neither is yet executed in formal detail)* — the four-state classification is exhaustive (Coverage Conjecture promoted).
- **T4 Type-Finite Foreclosure** — door-space is type-finite even when carrier-space is infinite.
- **T5 Attack Foreclosure (v4)** *(candidate — derivation from T1+T2+T6 is currently informal in M6 source; may require a separate axiom about the accepted-imports base)* — no internal cascade chain advances `X` without external content.
- **T6 CTMT Recursion** — terminal matrix-element families admit nested towers. (Open: track-independent depth bound — Branch B 8-layer chain at step 230 is the deepest documented instance.)

From the recognition-mode half (status: **validated two-instance meta-findings, paper-proposal-grade per M5 source**; individual PvNP and RH landings are theorem-grade under SB closure assumption, but the meta-template / signature / closure-content thesis are not yet theorem-grade as universal results — third-instance cross-track evidence and a structural argument from V-Differential column-membership to verdict pattern are required for theorem-grade lifting):
- **T7 Recognition-Mode Landing Template, Applicability** *(candidate meta-theorem)* — the seven-stage template lands at theorem-grade under SB closure assumption on V-Differential trace-state-only substrates; two-instance verified (PvNP, RH).
- **T8 Cross-Track Verdict Signature** *(candidate meta-theorem)* — `(ii)/(iii)/(ii)` for options 1/2/3 of the three-option derivation sweep on TSO substrates; two-instance verified, corpus-pending.
- **T9 Closure-Content Thesis** *(candidate meta-theorem)* — load-bearing structural content for TSO closures is content of formed-layer closure per Foundations I, not separately-derivable from currently-available primitives.
- **T10 Attack Foreclosure (v5 refinement)** *(candidate; refines T5 v4)* — derivation routes foreclosed per v4; recognition-mode landings are structurally distinct and achieve theorem-grade.

From the calibration-family half (PvNP-derived, framework-general):
- **T11 Calibration-Family Structure** — the non-descending discipline is family-typed; 11+ valid calibrations + 5 honest retracts on the P vs NP track.
- **T12 Rebadge Discipline** — a candidate calibration that matches an existing member on all four axes collapses on earning-its-place.
- **T13 Bridges-as-Theorems** — bridges between calibrations are typed objects with content (basis-change OR substantive theorem), not free amalgamations.
- **T14 Bridge Type-Direction** — bridges have typed direction; existence ≠ usability.
- **T15 Coverage-Family Geometry** — calibration union has typed holes; more calibrations is not monotonically more closure power.
- **T16 Framework-Type Self-Characterization** — the cascade's natural object-type vs Clay-target type, separated by three named functorial gates.
- **T17 Named Functorial Gates** — a new typed-deposit species: typed-bridges-as-content with stated theorem obligation.

## Dependencies (imported, not re-derived)

- Paper 1 (Adequacy Residuals): the `Ξ_C(D | L)` Schur calculus.
- Paper 2 (SDTC): the duality-confinement membrane theorem (apparatus); cited as recognition-source provider for RH (paper 6).
- Paper 3 (AOR): the eight-stratum defect / refinement-stable hierarchy bookkeeping language.
- Paper 4 (Needle Killer): the layer-dissolving endpoint and the all-six taxonomy.
- Paper 5 (NS): provides the witness-content-exposing column derivation-route landing as control case.
- Paper 6 (RH): provides one of two recognition-mode landing instances.
- Paper 7 (P vs NP): provides the other recognition-mode landing instance; Class-B Irremovability barrier referenced.
- Paper 8 (Hiddenness CSL): provides the recognition source `Γ_csl-sat-hidden` consumed by paper 7.
- Foundations I/II/III: closure formation, seven-schema admissibility, BirdInt judgments, finite rotating audit.

## Explicit nonclaims

- Not a proof of any Clay-class problem (those are the sibling papers).
- Not a claim that recognition-mode is weaker than derivation-mode (peers under the SB closure assumption).
- Not a claim that the `(ii)/(iii)/(ii)` signature is universal (two-instance evidence, predictive only).
- Not a refutation of v4 Attack Foreclosure (refinement, not replacement).
- Not a standard-ZFC unconditional proof of anything.
- Not a final form: theorem-grade lifting requires (a) third-instance cross-track verification, (b) structural argument from V-Differential column-membership to verdict pattern.

## Statement Source Map

- `paper/meta_math/proposal.md` records the structural contract and scope for the merged M5+M6 paper.
- M6 supplies the Part I foreclosure statements and the Part III calibration-family statements.
- M5 supplies the Part II recognition-mode landing statements, scoped to NS/RH/PvNP.
- `paper/meta_math/paper_inventory.toml`, `paper/meta_math/notes/statements-of-record.yml`, the Lean manifest, and the trust base are the canonical public support records for statement coverage and mechanization status.
- The sibling substrate papers are referenced through `paper/references.bib` rather than by archive path.

## Pending work before manuscript

1. Strip BSD/Hodge content from M6 source; replace cross-track validation rows with NS/RH/PvNP-only versions.
2. Position M6 Theorem 7 (Non-Descending Translation) relative to Paper 7's recognition-mode landing — M6 T7's translation/handoff mechanism is structurally distinct from Paper 7's recognition-source landing route, so M6 T7 is **not the path Paper 7 took**, not a superseded claim. Its validation-obstruction evidence and calibration/retract catalog remain relevant calibration-family substrate. Fold M6 T7 into Part III as the historical / substrate-grounding context for the Calibration Family, with explicit note that it is a distinct framework move from the recognition-mode template.
3. Decide whether Part III (Calibration Family) stays in the main paper or spins off as a separate companion (decision point at first complete draft; if main paper exceeds ~80 pages, spin off).
4. Cross-paper consistency audit with sibling papers 2/6/7/8 (Section 7).
5. **Formal proof obligations on T3 (Coverage Theorem)**: (i) precise definition of "open conjecture relative to accepted-imports base"; (ii) relative-consistency argument `CRE + closure-from-base ⟹ X ∈ base`. Per M6 source, neither move has been executed in formal detail.
6. **Formal derivation of T5 (Attack Foreclosure v4)** from T1+T2+T6 (CTMT recursion). Per M6 source, the derivation is currently informal; may require a separate axiom about the framework's accepted-imports base. If a separate axiom is required, state it explicitly and assess relative-consistency.
7. **Tautology / falsifiability guard** on T1–T6 cluster. Per M6 source, as typed conditions have been refined (CTMT → CTMT recursion; Carrier Dichotomy → Selberg-Class Dichotomy Generalization), they have become more accommodating; the paper must exhibit at least one counterexample-shape the framework identifies as *not in CRCFT mode* to demonstrate falsifiability. Conrey-1989 falsification attempt in M6 record is a starting point; a broader counterexample search is needed.
8. **Theorem-grade lifting of T7–T10** (recognition-mode meta-claims). Per M5 source, requires (a) third-instance cross-track verification (Hodge or another track in V-Differential TSO column attempted via the template) and (b) a structural argument from V-Differential column-membership to the verdict pattern — currently the `(ii)/(iii)/(ii)` signature is empirically observed only.
9. **Bridge composition open question** (M6 Open Question 4): composite state of two CRE carriers in different CRCFT modes, or two non-CRE carriers via typed bridge. Possibly a new theorem; decide whether to include or defer.
