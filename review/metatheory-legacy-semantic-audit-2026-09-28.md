# Retained metatheory Lean: semantic audit checkpoint — 2026-09-28

This is a self-review of the 20 retained `SixBirdsMetaMath.MetaMath` modules,
separate from the new RH–Navier analytic theorem. Exact module bytes are in
`metatheory-legacy-source-hashes-2026-09-28.txt`. The full metatheory
validator passed its 3843-job build in
`metatheory-full-lean-validator-2026-09-28.log`. Compilation establishes
the stated Lean implications; the source review below classifies what
those implications actually say.

| Paper rows | Lean status and precise content |
| --- | --- |
| T1 Carrier Dichotomy | `carrier_dichotomy` proves the non-target-equivalent branch from a supplied sound accepted-import base. The target-equivalent three-way classification calls `carrier_dichotomy_t3_pending`, an open axiom under opaque `CoverageContext`. |
| T2 Bridge Impossibility | `bridge_impossibility` invokes T1 and the open axiom `bridge_impossibility_carries_obligation`. Its `_hCNonX` and `_hCNative` inputs are unused in the proof term; the claimed bridge obligation is supplied by that axiom once the composite is classified. It is not a theorem showing every real mathematical bridge pays target strength. |
| T3 Coverage and T4 Type-Finite Foreclosure | `coverage_theorem` is an open axiom. `type_finite_foreclosure` and `classify_spec` select one of four constructors from it. The finite type is an honest classification *conditional on coverage*, not a proof that actual attempted carriers exhaust those four cases. |
| T5 Attack Foreclosure v4 | `attack_foreclosure_v4` is an open axiom about opaque internal-move semantics and opaque framework scope. It cannot establish a mathematical impossibility outside those supplied meanings. |
| T6 CTMT Recursion | `ctmt_recursion` proves base and step laws for an inductively defined tower under a supplied reduction relation. It does not construct a matrix-family reduction in an application. |
| T7–T10 Recognition Mode | All four principal statements are open axioms: `recognition_template_applicability`, `verdict_signature`, `closure_content_thesis`, and `attack_foreclosure_v5`. `SevenStageTemplate` stores seven `Prop` fields, while `TemplateApplies`, formed closure, column membership, and landing are opaque. No actual RH, Navier or PvNP source is produced by these axioms. |
| T11–T15 Calibration Family | These are standard-axiom-free facts about supplied string/list/record definitions: 13 seeded labels, a four-string rebadge test, a two-constructor bridge kind, source/target reversal, and membership in a declared coverage list. They do not prove actual complexity-class coverage or bridge existence. In T11 the second conjunct has conclusion `True` for each candidate; it does not characterize all future calibrations. |
| T16 and T17 | `framework_type_self_characterization` proves mismatch of two manually specified four-string PvNP records plus the count of three named gates. The framework-general mismatch is a distinct open axiom, `framework_type_self_char_pending`. `named_functorial_gates` proves that the declared list has three nonempty names/obligation strings; no functorial transport theorem is built. |

The exact trust register `lean/manifests/legacy_obligations.toml` lists nine
metatheory obligation axioms, one separate Foundations IV axiom, and 25
uninterpreted legacy interface declarations. The paper's existing
formalization appendix already discloses the nine metatheory obligations
and distinguishes partial from theorem rows. That disclosure should be
preserved and made visible wherever the revised main text discusses the
old classification or recognition claims.

The new `SixBirdsMetaMath.RHNavier` modules import maintained Needles and
RH/DC modules directly. Their eight printed analytic exports depend only on
`propext`, `Classical.choice`, and `Quot.sound`; none draws on the nine
metatheory obligation axioms. The concrete joint observation and return
theorem therefore has a different proof status from T1–T10's open schemas.

## Manuscript reconciliation required

The current `paper/meta_math/sections/sec_09_scope.tex` says BSD has no
substrate paper in the Tsiokos corpus. The current local corpus has
`six-birds-bsd` with a BSD manuscript. Excluding BSD remains a
valid scope choice, but the reason must be updated after checking that
paper's exact status. The same section calls NS, RH, and PvNP three landed
conditional closures under an unspecified common SB assumption. The revised
paper must name each application premise and distinguish a formal
conditional composition from an independently supplied analytic source.
The bounded PvNP cross-check finds that
`six-birds-hiddenness/paper/pvnp/sections/sec_11_judgment.tex` explicitly
labels its `BirdInt` judgment a manifest obligation at recognition grade.
`SixBirdsHiddenness.PvNP.ContradictionChain.fourStepContradictionConditional`
proves an implication from supplied SAT-in-P/currentization biconditionals
and a supplied recognition-source negation; `satInNP` transports supplied
verifier facts rather than constructing a SAT encoding. The PvNP paper
states this conditional scope. Its `GateAudit.gateAudit` consumes a record
whose seven evidence fields and evidence-to-non-smuggling implications are
inputs. Thus PvNP is a cited conditional architecture, but these Lean
exports do not prove the metatheory's universal T7–T10 claims or certify
that an independent hiddenness source exists. The phrase “two-instance
verified” should be qualified to say exactly which substrate records and
conditional implications are checked. This bounded audit does not reopen
the PvNP campaign.

The seven-paper claim map and final manuscript review are still open.
