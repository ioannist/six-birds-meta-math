import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure
import SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Locality

/-!
F49 Common-Source / Nonlocal Correlation Normal Form.

A correlation is structurally explained only when its joint residual is carried
by a declared common source, a lawful directed route, or a declared shared
interface. If none of those role-specific factorization records is supplied,
the dependency remains a statused residual, and nonlocality is always relative
to a declared locality package.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.CommonSourceNonlocal

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
open SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure

/-- The joint readout `(a, b)` of two local probes. -/
def jointReadout {H A B : Type} (readoutA : H → A) (readoutB : H → B) :
    H → A × B :=
  fun h => (readoutA h, readoutB h)

/-- The quotient carrying a declared common source together with the two local
access packages. -/
def commonSourceCorrelationQuotient {H S LA LB : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB) : H → (S × LA) × LB :=
  fun h => ((source h, leftAccess h), rightAccess h)

/-- The quotient carrying a shared interface together with the two local access
packages. -/
def interfaceCorrelationQuotient {H I LA LB : Type} (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB) : H → (I × LA) × LB :=
  fun h => ((sharedInterface h, leftAccess h), rightAccess h)

/-- Common-source explanation at the joint-residual layer: the joint readout
descends through `(source, leftAccess, rightAccess)`. -/
def CommonSourceFactorization {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  Descends (commonSourceCorrelationQuotient source leftAccess rightAccess)
    (fun h : H => h) (jointReadout readoutA readoutB)

/-- Common-source obstruction: same source and local data, different joint
readout. -/
def CommonSourceObstruction {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : (H × H) → Prop :=
  splitPairObstruction
    (commonSourceCorrelationQuotient source leftAccess rightAccess)
    (fun h : H => h) (jointReadout readoutA readoutB)

/-- No common-source obstruction is present. -/
def CommonSourceObstructionEmpty {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  ObstructionEmpty
    (CommonSourceObstruction source leftAccess rightAccess readoutA readoutB)

/-- Deterministic local response maps for a common source. This is stronger
than bare joint descent and records the source's role as a shared cause rather
than an untyped joint interface. -/
def CommonSourceResponseStructure {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  ∃ responseA : S × LA → A, ∃ responseB : S × LB → B,
    responseA ∘ (fun h : H => (source h, leftAccess h)) = readoutA ∧
      responseB ∘ (fun h : H => (source h, rightAccess h)) = readoutB

/-- A role-declared common-source explanation supplies both joint descent and
the local response structure. -/
def CommonSourceExplanation {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  CommonSourceFactorization source leftAccess rightAccess readoutA readoutB ∧
    CommonSourceResponseStructure source leftAccess rightAccess readoutA readoutB

/-- Interface-mediated explanation: the joint readout descends through the
shared interface and local packages. -/
def InterfaceMediatedFactorization {H I LA LB A B : Type}
    (sharedInterface : H → I) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  Descends (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)
    (fun h : H => h) (jointReadout readoutA readoutB)

/-- Interface obstruction: same interface and local data, different joint
readout. -/
def InterfaceMediatedObstruction {H I LA LB A B : Type}
    (sharedInterface : H → I) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : (H × H) → Prop :=
  splitPairObstruction
    (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)
    (fun h : H => h) (jointReadout readoutA readoutB)

/-- No interface-mediated obstruction is present. -/
def InterfaceMediatedObstructionEmpty {H I LA LB A B : Type}
    (sharedInterface : H → I) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  ObstructionEmpty
    (InterfaceMediatedObstruction sharedInterface leftAccess rightAccess readoutA readoutB)

/-- Route transport descent for a declared directed route/intervention package.
The route is not mere order: admissibility and stability are separate records. -/
def DirectRouteFactorization {RouteContext RouteQuotient RouteTarget Residue : Type}
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue) : Prop :=
  Descends routeQuotient routeTransport targetResidue

/-- Direct-route obstruction: same route quotient, different target residue. -/
def DirectRouteObstruction {RouteContext RouteQuotient RouteTarget Residue : Type}
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue) : (RouteContext × RouteContext) → Prop :=
  splitPairObstruction routeQuotient routeTransport targetResidue

/-- No direct-route obstruction is present. -/
def DirectRouteObstructionEmpty {RouteContext RouteQuotient RouteTarget Residue : Type}
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue) : Prop :=
  ObstructionEmpty (DirectRouteObstruction routeQuotient routeTransport targetResidue)

/-- A role-declared direct-route explanation records admissibility, stability,
and route descent. -/
def DirectRouteExplanation {RouteContext RouteQuotient RouteTarget Residue : Type}
    (routeAdmissible routeStable : Prop)
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue) : Prop :=
  routeAdmissible ∧ routeStable ∧
    DirectRouteFactorization routeQuotient routeTransport targetResidue

/-- F49 common-source fiber test: each local readout is constant on fibers of
the source together with its own local access quotient. -/
def PaperCommonSourceFibers {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  PackageClosed (fun h : H => (source h, leftAccess h)) readoutA ∧
    PackageClosed (fun h : H => (source h, rightAccess h)) readoutB

/-- F49 interface fiber test for the joint readout. -/
def PaperInterfaceFibers {H I LA LB A B : Type}
    (sharedInterface : H → I) (leftAccess : H → LA)
    (rightAccess : H → LB) (readoutA : H → A) (readoutB : H → B) : Prop :=
  PackageClosed
    (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)
    (jointReadout readoutA readoutB)

/-- F49 route fiber test: the route quotient is on the same history carrier
as the correlation, and it determines that very joint readout. -/
def PaperDirectRouteFibers {H P A B : Type} (routeQuotient : H → P)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  PackageClosed routeQuotient (jointReadout readoutA readoutB)

/-- F49's direct-route explanation before converting fiber constancy to a
total response map. -/
def PaperDirectRoute {H P A B : Type} (routeAdmissible routeStable : Prop)
    (routeQuotient : H → P) (readoutA : H → A) (readoutB : H → B) : Prop :=
  routeAdmissible ∧ routeStable ∧
    PaperDirectRouteFibers routeQuotient readoutA readoutB

/-- A source is hidden from current observation when it does not descend through
the current access quotient. -/
def HiddenCommonSource {H Current S : Type} (currentAccess : H → Current)
    (source : H → S) : Prop :=
  ¬ Descends currentAccess (fun h : H => h) source

/-- Product independence is the null-correlation baseline: the declared
correlation residual vanishes. -/
def ProductIndependence (residualVanishes : Prop) : Prop :=
  residualVanishes

/-- Accepted correlation explanation is a role-declared source, route, or
interface record. -/
def AcceptedCorrelationExplanation (commonSource directRoute sharedInterface : Prop) :
    Prop :=
  commonSource ∨ directRoute ∨ sharedInterface

/-- If no explanatory role is supplied, a present dependency is a statused
correlation residual, not an explained relation. -/
def CorrelationResidual (correlationPresent commonSource directRoute sharedInterface :
    Prop) : Prop :=
  correlationPresent ∧ ¬ commonSource ∧ ¬ directRoute ∧ ¬ sharedInterface

/-- Nonlocal residual status is locality-relative: it is a residual dependency
plus failure of the declared locality package. -/
def NonlocalCorrelationResidual (correlationPresent localityPackage commonSource
    directRoute sharedInterface : Prop) : Prop :=
  CorrelationResidual correlationPresent commonSource directRoute sharedInterface ∧
    ¬ localityPackage

/-- Source status vocabulary for common-source and nonlocal-correlation claims. -/
inductive CorrelationStatus where
  | productIndependence
  | commonSource
  | hiddenCommonSource
  | probabilisticCommonSource
  | directRoute
  | bidirectionalRoute
  | feedbackCorrelation
  | interfaceMediated
  | boundaryMediated
  | horizonMediated
  | bridgeMediatedCorrelation
  | localityResidual
  | nonlocalCorrelationResidual
  | correlationResidual
  | commonSourceFailure
  | routeFailure
  | interfaceLeakage
  | contextCoupledSource
  | selectionConditionedCorrelation
  | postselectedCorrelation
  | presentationCorrelationArtifact
  | protocolCorrelationArtifact
  | topologicalCorrelation
  | anomalyMediatedCorrelation
  | correlationDualityMismatch
  | correlationOverread
deriving DecidableEq

/-- Meaning assignment for the F49 correlation status vocabulary. -/
def CorrelationStatusHolds (product commonSource hiddenSource probabilisticSource
    directRoute bidirectional feedback interface boundary horizon bridge localityResidual
    nonlocalResidual residual sourceFailure routeFailure interfaceLeakage
    contextCoupled selectionConditioned postselected presentationArtifact protocolArtifact
    topological anomalyMediated dualityMismatch overread : Prop) :
    CorrelationStatus → Prop
  | CorrelationStatus.productIndependence => product
  | CorrelationStatus.commonSource => commonSource
  | CorrelationStatus.hiddenCommonSource => hiddenSource
  | CorrelationStatus.probabilisticCommonSource => probabilisticSource
  | CorrelationStatus.directRoute => directRoute
  | CorrelationStatus.bidirectionalRoute => bidirectional
  | CorrelationStatus.feedbackCorrelation => feedback
  | CorrelationStatus.interfaceMediated => interface
  | CorrelationStatus.boundaryMediated => boundary
  | CorrelationStatus.horizonMediated => horizon
  | CorrelationStatus.bridgeMediatedCorrelation => bridge
  | CorrelationStatus.localityResidual => localityResidual
  | CorrelationStatus.nonlocalCorrelationResidual => nonlocalResidual
  | CorrelationStatus.correlationResidual => residual
  | CorrelationStatus.commonSourceFailure => sourceFailure
  | CorrelationStatus.routeFailure => routeFailure
  | CorrelationStatus.interfaceLeakage => interfaceLeakage
  | CorrelationStatus.contextCoupledSource => contextCoupled
  | CorrelationStatus.selectionConditionedCorrelation => selectionConditioned
  | CorrelationStatus.postselectedCorrelation => postselected
  | CorrelationStatus.presentationCorrelationArtifact => presentationArtifact
  | CorrelationStatus.protocolCorrelationArtifact => protocolArtifact
  | CorrelationStatus.topologicalCorrelation => topological
  | CorrelationStatus.anomalyMediatedCorrelation => anomalyMediated
  | CorrelationStatus.correlationDualityMismatch => dualityMismatch
  | CorrelationStatus.correlationOverread => overread

/-- A common-source quotient has the expected split-pair normal form. -/
theorem common_source_factorization_iff_no_obstruction {H S LA LB A B : Type}
    (source : H → S) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (hsource :
      Function.Surjective
        (commonSourceCorrelationQuotient source leftAccess rightAccess)) :
    CommonSourceFactorization source leftAccess rightAccess readoutA readoutB ↔
      CommonSourceObstructionEmpty source leftAccess rightAccess readoutA readoutB :=
  descent_repair_normal_form
    (commonSourceCorrelationQuotient source leftAccess rightAccess)
    (fun h : H => h) (jointReadout readoutA readoutB) hsource

/-- Separate local response maps induce joint common-source factorization. -/
theorem separate_common_source_responses_factor {H S LA LB A B : Type}
    (source : H → S) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (hresponses :
      CommonSourceResponseStructure source leftAccess rightAccess readoutA readoutB) :
    CommonSourceFactorization source leftAccess rightAccess readoutA readoutB := by
  rcases hresponses with ⟨responseA, responseB, hA, hB⟩
  refine ⟨fun data => (responseA data.1, responseB (data.1.1, data.2)), ?_⟩
  funext h
  exact Prod.ext (congrFun hA h) (congrFun hB h)

/-- A role-declared common-source explanation is obstruction-free plus the
separate local response record. -/
theorem common_source_explanation_iff {H S LA LB A B : Type} (source : H → S)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (hsource :
      Function.Surjective
        (commonSourceCorrelationQuotient source leftAccess rightAccess)) :
    CommonSourceExplanation source leftAccess rightAccess readoutA readoutB ↔
      CommonSourceObstructionEmpty source leftAccess rightAccess readoutA readoutB ∧
        CommonSourceResponseStructure source leftAccess rightAccess readoutA readoutB := by
  constructor
  · intro h
    exact ⟨(common_source_factorization_iff_no_obstruction source leftAccess
      rightAccess readoutA readoutB hsource).1 h.1, h.2⟩
  · intro h
    exact ⟨(common_source_factorization_iff_no_obstruction source leftAccess
      rightAccess readoutA readoutB hsource).2 h.1, h.2⟩

/-- Interface-mediated correlation has the same descent/obstruction normal form
with a role-declared interface quotient. -/
theorem interface_mediated_iff_no_obstruction {H I LA LB A B : Type}
    (sharedInterface : H → I) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (hinterface :
      Function.Surjective
        (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)) :
    InterfaceMediatedFactorization sharedInterface leftAccess rightAccess readoutA readoutB ↔
      InterfaceMediatedObstructionEmpty sharedInterface leftAccess rightAccess
        readoutA readoutB :=
  descent_repair_normal_form
    (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)
    (fun h : H => h) (jointReadout readoutA readoutB) hinterface

/-- Direct-route explanation is route admissibility and stability plus absence
of route-descent obstruction. -/
theorem direct_route_explanation_iff_no_obstruction
    {RouteContext RouteQuotient RouteTarget Residue : Type}
    (routeAdmissible routeStable : Prop)
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue)
    (hroute : Function.Surjective routeQuotient) :
    DirectRouteExplanation routeAdmissible routeStable routeQuotient routeTransport
        targetResidue ↔
      routeAdmissible ∧ routeStable ∧
        DirectRouteObstructionEmpty routeQuotient routeTransport targetResidue := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1,
      (descent_repair_normal_form routeQuotient routeTransport targetResidue hroute).1
        h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1,
      (descent_repair_normal_form routeQuotient routeTransport targetResidue hroute).2
        h.2.2⟩

/-- Accepted explanations are exactly the declared source, route, or interface
records. -/
theorem accepted_correlation_explanation_iff (commonSource directRoute
    sharedInterface : Prop) :
    AcceptedCorrelationExplanation commonSource directRoute sharedInterface ↔
      commonSource ∨ directRoute ∨ sharedInterface := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Residual classification is the complement of supplied explanatory roles
for a present dependency. -/
theorem correlation_residual_iff (correlationPresent commonSource directRoute
    sharedInterface : Prop) :
    CorrelationResidual correlationPresent commonSource directRoute sharedInterface ↔
      correlationPresent ∧ ¬ commonSource ∧ ¬ directRoute ∧ ¬ sharedInterface := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Nonlocal residual classification is residual status plus failure of the
declared locality package. -/
theorem nonlocal_correlation_residual_iff (correlationPresent localityPackage
    commonSource directRoute sharedInterface : Prop) :
    NonlocalCorrelationResidual correlationPresent localityPackage commonSource
        directRoute sharedInterface ↔
      correlationPresent ∧ ¬ commonSource ∧ ¬ directRoute ∧ ¬ sharedInterface ∧
        ¬ localityPackage := by
  constructor
  · intro h
    rcases h with ⟨hresidual, hlocality⟩
    exact ⟨hresidual.1, hresidual.2.1, hresidual.2.2.1, hresidual.2.2.2,
      hlocality⟩
  · intro h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

/--
Common-Source / Nonlocal Correlation Normal Form. Common-source,
direct-route, and interface-mediated explanations are role-declared quotient
descent records with corresponding split-pair obstructions; if none is
supplied, a present dependency is only a residual, and it becomes nonlocal only
relative to a failed locality package.
-/
theorem common_source_nonlocal_correlation
    {H S I LA LB A B RouteContext RouteQuotient RouteTarget Residue : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable correlationPresent localityPackage : Prop)
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue)
    (hsource :
      Function.Surjective
        (commonSourceCorrelationQuotient source leftAccess rightAccess))
    (hinterface :
      Function.Surjective
        (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess))
    (hroute : Function.Surjective routeQuotient) :
    (CommonSourceFactorization source leftAccess rightAccess readoutA readoutB ↔
      CommonSourceObstructionEmpty source leftAccess rightAccess readoutA readoutB) ∧
      (CommonSourceExplanation source leftAccess rightAccess readoutA readoutB ↔
        CommonSourceObstructionEmpty source leftAccess rightAccess readoutA readoutB ∧
          CommonSourceResponseStructure source leftAccess rightAccess readoutA readoutB) ∧
        (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
            readoutA readoutB ↔
          InterfaceMediatedObstructionEmpty sharedInterface leftAccess rightAccess
            readoutA readoutB) ∧
          (DirectRouteExplanation routeAdmissible routeStable routeQuotient
              routeTransport targetResidue ↔
            routeAdmissible ∧ routeStable ∧
              DirectRouteObstructionEmpty routeQuotient routeTransport targetResidue) ∧
            (AcceptedCorrelationExplanation
                (CommonSourceExplanation source leftAccess rightAccess readoutA readoutB)
                (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                  routeTransport targetResidue)
                (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                  readoutA readoutB) ↔
              CommonSourceExplanation source leftAccess rightAccess readoutA readoutB ∨
                DirectRouteExplanation routeAdmissible routeStable routeQuotient
                  routeTransport targetResidue ∨
                  InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                    readoutA readoutB) ∧
              (CorrelationResidual correlationPresent
                  (CommonSourceExplanation source leftAccess rightAccess readoutA readoutB)
                  (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                    routeTransport targetResidue)
                  (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                    readoutA readoutB) ↔
                correlationPresent ∧
                  ¬ CommonSourceExplanation source leftAccess rightAccess readoutA readoutB ∧
                    ¬ DirectRouteExplanation routeAdmissible routeStable routeQuotient
                      routeTransport targetResidue ∧
                      ¬ InterfaceMediatedFactorization sharedInterface leftAccess
                        rightAccess readoutA readoutB) ∧
                (NonlocalCorrelationResidual correlationPresent localityPackage
                    (CommonSourceExplanation source leftAccess rightAccess readoutA readoutB)
                    (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                      routeTransport targetResidue)
                    (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                      readoutA readoutB) ↔
                  correlationPresent ∧
                    ¬ CommonSourceExplanation source leftAccess rightAccess readoutA
                      readoutB ∧
                      ¬ DirectRouteExplanation routeAdmissible routeStable routeQuotient
                        routeTransport targetResidue ∧
                        ¬ InterfaceMediatedFactorization sharedInterface leftAccess
                          rightAccess readoutA readoutB ∧
                          ¬ localityPackage) := by
  refine ⟨common_source_factorization_iff_no_obstruction source leftAccess
    rightAccess readoutA readoutB hsource, ?_⟩
  refine ⟨common_source_explanation_iff source leftAccess rightAccess readoutA readoutB
    hsource, ?_⟩
  refine ⟨interface_mediated_iff_no_obstruction sharedInterface leftAccess rightAccess
    readoutA readoutB hinterface, ?_⟩
  refine ⟨direct_route_explanation_iff_no_obstruction routeAdmissible routeStable
    routeQuotient routeTransport targetResidue hroute, ?_⟩
  refine ⟨accepted_correlation_explanation_iff _ _ _, ?_⟩
  refine ⟨correlation_residual_iff _ _ _ _, ?_⟩
  exact nonlocal_correlation_residual_iff _ _ _ _ _

/-- The repaired F49 statement: separate local response maps, a joint
interface readout, the route gate, and locality-relative residual status. -/
theorem common_source_nonlocal_correlation_paper
    {H S I LA LB A B RouteContext RouteQuotient RouteTarget Residue : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable correlationPresent localityPackage : Prop)
    (routeQuotient : RouteContext → RouteQuotient)
    (routeTransport : RouteContext → RouteTarget)
    (targetResidue : RouteTarget → Residue)
    (hsource : Function.Surjective
      (commonSourceCorrelationQuotient source leftAccess rightAccess))
    (hinterface : Function.Surjective
      (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess))
    (hroute : Function.Surjective routeQuotient) :
    (CommonSourceResponseStructure source leftAccess rightAccess readoutA readoutB ↔
      ∃ responseA : S × LA → A, ∃ responseB : S × LB → B,
        responseA ∘ (fun h : H => (source h, leftAccess h)) = readoutA ∧
          responseB ∘ (fun h : H => (source h, rightAccess h)) = readoutB) ∧
      (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
          readoutA readoutB ↔
        ∃ response : (I × LA) × LB → A × B,
          response ∘ (interfaceCorrelationQuotient sharedInterface
            leftAccess rightAccess) = jointReadout readoutA readoutB) ∧
        (DirectRouteExplanation routeAdmissible routeStable routeQuotient
            routeTransport targetResidue ↔
          routeAdmissible ∧ routeStable ∧
            DirectRouteFactorization routeQuotient routeTransport targetResidue) ∧
          (AcceptedCorrelationExplanation
              (CommonSourceResponseStructure source leftAccess rightAccess
                readoutA readoutB)
              (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                routeTransport targetResidue)
              (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                readoutA readoutB) ↔
            CommonSourceResponseStructure source leftAccess rightAccess
                readoutA readoutB ∨
              DirectRouteExplanation routeAdmissible routeStable routeQuotient
                routeTransport targetResidue ∨
              InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                readoutA readoutB) ∧
            (CorrelationResidual correlationPresent
                (CommonSourceResponseStructure source leftAccess rightAccess
                  readoutA readoutB)
                (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                  routeTransport targetResidue)
                (InterfaceMediatedFactorization sharedInterface leftAccess rightAccess
                  readoutA readoutB) ↔
              correlationPresent ∧
                ¬ AcceptedCorrelationExplanation
                  (CommonSourceResponseStructure source leftAccess rightAccess
                    readoutA readoutB)
                  (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                    routeTransport targetResidue)
                  (InterfaceMediatedFactorization sharedInterface leftAccess
                    rightAccess readoutA readoutB)) ∧
              (NonlocalCorrelationResidual correlationPresent localityPackage
                  (CommonSourceResponseStructure source leftAccess rightAccess
                    readoutA readoutB)
                  (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                    routeTransport targetResidue)
                  (InterfaceMediatedFactorization sharedInterface leftAccess
                    rightAccess readoutA readoutB) ↔
                CorrelationResidual correlationPresent
                  (CommonSourceResponseStructure source leftAccess rightAccess
                    readoutA readoutB)
                  (DirectRouteExplanation routeAdmissible routeStable routeQuotient
                    routeTransport targetResidue)
                  (InterfaceMediatedFactorization sharedInterface leftAccess
                    rightAccess readoutA readoutB) ∧ ¬ localityPackage) := by
  let _ := hsource
  let _ := hinterface
  let _ := hroute
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp only [CorrelationResidual, AcceptedCorrelationExplanation, not_or]
  · rfl

/-- F49 with the direct route on `H` and tied to the joint readout. The
nonempty history hypothesis is needed to derive surjectivity of the two local
pair quotients from the surjective triple quotient; without it the
fiber-to-total-map argument has an empty-carrier counterexample. -/
theorem common_source_nonlocal_correlation_repaired
    {H S I LA LB A B P : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable correlationPresent localityPackage : Prop)
    (routeQuotient : H → P)
    (hH : Nonempty H)
    (hsource : Function.Surjective
      (commonSourceCorrelationQuotient source leftAccess rightAccess))
    (hinterface : Function.Surjective
      (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess))
    (hroute : Function.Surjective routeQuotient) :
    (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB ↔
      ∃ responseA : S × LA → A, ∃ responseB : S × LB → B,
        responseA ∘ (fun h : H => (source h, leftAccess h)) = readoutA ∧
          responseB ∘ (fun h : H => (source h, rightAccess h)) = readoutB) ∧
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess
          readoutA readoutB ↔
        ∃ response : (I × LA) × LB → A × B,
          response ∘ (interfaceCorrelationQuotient sharedInterface
            leftAccess rightAccess) = jointReadout readoutA readoutB) ∧
        (PaperDirectRoute routeAdmissible routeStable routeQuotient
            readoutA readoutB ↔
          routeAdmissible ∧ routeStable ∧
            ∃ response : P → A × B,
              response ∘ routeQuotient = jointReadout readoutA readoutB) ∧
          (AcceptedCorrelationExplanation
              (PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB)
              (PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB)
              (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ↔
            PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB ∨
              PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB ∨
              PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ∧
            (CorrelationResidual correlationPresent
                (PaperCommonSourceFibers source leftAccess rightAccess
                  readoutA readoutB)
                (PaperDirectRoute routeAdmissible routeStable routeQuotient
                  readoutA readoutB)
                (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                  readoutA readoutB) ↔
              correlationPresent ∧
                ¬ AcceptedCorrelationExplanation
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB)) ∧
              (NonlocalCorrelationResidual correlationPresent localityPackage
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ↔
                CorrelationResidual correlationPresent
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ∧ ¬ localityPackage) := by
  rcases hH with ⟨history⟩
  have hleft : Function.Surjective
      (fun h : H => (source h, leftAccess h)) := by
    intro pair
    rcases hsource (pair, rightAccess history) with ⟨h, hh⟩
    exact ⟨h, congrArg Prod.fst hh⟩
  have hright : Function.Surjective
      (fun h : H => (source h, rightAccess h)) := by
    intro pair
    rcases hsource ((pair.1, leftAccess history), pair.2) with ⟨h, hh⟩
    exact ⟨h, Prod.ext (congrArg (fun x => x.1.1) hh)
      (congrArg (fun x : (S × LA) × LB => x.2) hh)⟩
  have hA := (sufficiency_closure
    (fun h : H => (source h, leftAccess h)) readoutA hleft).1
  have hB := (sufficiency_closure
    (fun h : H => (source h, rightAccess h)) readoutB hright).1
  have hI := (sufficiency_closure
    (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)
    (jointReadout readoutA readoutB) hinterface).1
  have hR := (sufficiency_closure routeQuotient
    (jointReadout readoutA readoutB) hroute).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      rcases h with ⟨ha, hb⟩
      rcases hA.mp ha with ⟨responseA, eqA⟩
      rcases hB.mp hb with ⟨responseB, eqB⟩
      exact ⟨responseA, responseB, eqA, eqB⟩
    · rintro ⟨responseA, responseB, eqA, eqB⟩
      exact ⟨hA.mpr ⟨responseA, eqA⟩,
        hB.mpr ⟨responseB, eqB⟩⟩
  · exact hI
  · constructor
    · rintro ⟨hadmissible, hstable, hfibers⟩
      exact ⟨hadmissible, hstable, hR.mp hfibers⟩
    · rintro ⟨hadmissible, hstable, hfactor⟩
      exact ⟨hadmissible, hstable, hR.mpr hfactor⟩
  · rfl
  · simp only [CorrelationResidual, AcceptedCorrelationExplanation, not_or]
  · rfl

/-- The explicit paper correlation predicate: a joint local-access fiber
contains two different joint readouts. -/
def PaperCorrelation {H LA LB A B : Type}
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B) : Prop :=
  ∃ h h', (leftAccess h, rightAccess h) = (leftAccess h', rightAccess h') ∧
    jointReadout readoutA readoutB h ≠ jointReadout readoutA readoutB h'

/-- In the absence of a joint local-access split, every interface fiber
supports a well-defined joint readout. No surjectivity is required. -/
theorem no_correlation_interface_fibers {H I LA LB A B : Type}
    (sharedInterface : H → I) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (hno : ¬ PaperCorrelation leftAccess rightAccess readoutA readoutB) :
    PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB := by
  classical
  intro h h' heq
  apply Classical.byContradiction
  intro hreadout
  exact hno ⟨h, h', Prod.ext (congrArg (fun x => x.1.2) heq)
    (congrArg (fun x : (I × LA) × LB => x.2) heq), hreadout⟩

/-- Separate common-source fiber tests imply the joint interface fiber test
when the interface is that same source. -/
theorem common_source_interface_fibers {H S LA LB A B : Type}
    (source : H → S) (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (hsource : PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB) :
    PaperInterfaceFibers source leftAccess rightAccess readoutA readoutB := by
  intro h h' heq
  exact Prod.ext (hsource.1 h h' (congrArg Prod.fst heq))
    (hsource.2 h h' (Prod.ext (congrArg (fun x => x.1.1) heq)
      (congrArg (fun x : (S × LA) × LB => x.2) heq)))

/-- With the explicit paper correlation predicate, failure of all declared
explanations already forces correlation, so the residual needs no extra premise. -/
theorem correlation_residual_iff_not_locally_explainable
    {H S I LA LB A B P : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable : Prop) (routeQuotient : H → P) :
    CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
      (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB)
      (PaperDirectRoute routeAdmissible routeStable routeQuotient readoutA readoutB)
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB) ↔
    ¬ AcceptedCorrelationExplanation
      (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB)
      (PaperDirectRoute routeAdmissible routeStable routeQuotient readoutA readoutB)
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB) := by
  classical
  constructor
  · rintro ⟨_, hs, hr, hi⟩ (hs' | hr' | hi')
    · exact hs hs'
    · exact hr hr'
    · exact hi hi'
  · intro hno
    have hcorr : PaperCorrelation leftAccess rightAccess readoutA readoutB := by
      apply Classical.byContradiction
      intro hnot
      exact hno (Or.inr (Or.inr (no_correlation_interface_fibers
        sharedInterface leftAccess rightAccess readoutA readoutB hnot)))
    exact ⟨hcorr, fun hs => hno (Or.inl hs),
      fun hr => hno (Or.inr (Or.inl hr)), fun hi => hno (Or.inr (Or.inr hi))⟩

/-- The coverage statement extended by the new canonicality clauses. -/
theorem common_source_nonlocal_correlation_repaired_strengthened
    {H S I LA LB A B P : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable localityPackage : Prop)
    (routeQuotient : H → P)
    (hH : Nonempty H)
    (hsource : Function.Surjective
      (commonSourceCorrelationQuotient source leftAccess rightAccess))
    (hinterface : Function.Surjective
      (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess))
    (hroute : Function.Surjective routeQuotient) :
    ((PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB ↔
      ∃ responseA : S × LA → A, ∃ responseB : S × LB → B,
        responseA ∘ (fun h : H => (source h, leftAccess h)) = readoutA ∧
          responseB ∘ (fun h : H => (source h, rightAccess h)) = readoutB) ∧
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess
          readoutA readoutB ↔
        ∃ response : (I × LA) × LB → A × B,
          response ∘ (interfaceCorrelationQuotient sharedInterface
            leftAccess rightAccess) = jointReadout readoutA readoutB) ∧
        (PaperDirectRoute routeAdmissible routeStable routeQuotient
            readoutA readoutB ↔
          routeAdmissible ∧ routeStable ∧
            ∃ response : P → A × B,
              response ∘ routeQuotient = jointReadout readoutA readoutB) ∧
          (AcceptedCorrelationExplanation
              (PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB)
              (PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB)
              (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ↔
            PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB ∨
              PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB ∨
              PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ∧
            (CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
                (PaperCommonSourceFibers source leftAccess rightAccess
                  readoutA readoutB)
                (PaperDirectRoute routeAdmissible routeStable routeQuotient
                  readoutA readoutB)
                (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                  readoutA readoutB) ↔
              (PaperCorrelation leftAccess rightAccess readoutA readoutB) ∧
                ¬ AcceptedCorrelationExplanation
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB)) ∧
              (NonlocalCorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB) localityPackage
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ↔
                CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ∧ ¬ localityPackage)) ∧
    (∀ (I' : Type) (ι : H → I'),
      ¬ PaperCorrelation leftAccess rightAccess readoutA readoutB →
        PaperInterfaceFibers ι leftAccess rightAccess readoutA readoutB) ∧
    (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB →
      PaperInterfaceFibers source leftAccess rightAccess readoutA readoutB) ∧
    (CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
      (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB)
      (PaperDirectRoute routeAdmissible routeStable routeQuotient readoutA readoutB)
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB) ↔
    ¬ AcceptedCorrelationExplanation
      (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB)
      (PaperDirectRoute routeAdmissible routeStable routeQuotient readoutA readoutB)
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB)) := by
  exact ⟨common_source_nonlocal_correlation_repaired source sharedInterface
    leftAccess rightAccess readoutA readoutB routeAdmissible routeStable
    (PaperCorrelation leftAccess rightAccess readoutA readoutB) localityPackage
    routeQuotient hH hsource hinterface hroute,
    fun _ ι hno => no_correlation_interface_fibers ι leftAccess rightAccess
      readoutA readoutB hno,
    common_source_interface_fibers source leftAccess rightAccess readoutA readoutB,
    correlation_residual_iff_not_locally_explainable source sharedInterface
      leftAccess rightAccess readoutA readoutB routeAdmissible routeStable routeQuotient⟩

/-- The repaired F49 law needs only a nonempty history carrier: values off
the source, interface, and route images use a history readout as default. -/
theorem common_source_nonlocal_correlation_repaired_of_nonempty
    {H S I LA LB A B P : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable correlationPresent localityPackage : Prop)
    (routeQuotient : H → P)
    (hH : Nonempty H)
 :
    (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB ↔
      ∃ responseA : S × LA → A, ∃ responseB : S × LB → B,
        responseA ∘ (fun h : H => (source h, leftAccess h)) = readoutA ∧
          responseB ∘ (fun h : H => (source h, rightAccess h)) = readoutB) ∧
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess
          readoutA readoutB ↔
        ∃ response : (I × LA) × LB → A × B,
          response ∘ (interfaceCorrelationQuotient sharedInterface
            leftAccess rightAccess) = jointReadout readoutA readoutB) ∧
        (PaperDirectRoute routeAdmissible routeStable routeQuotient
            readoutA readoutB ↔
          routeAdmissible ∧ routeStable ∧
            ∃ response : P → A × B,
              response ∘ routeQuotient = jointReadout readoutA readoutB) ∧
          (AcceptedCorrelationExplanation
              (PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB)
              (PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB)
              (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ↔
            PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB ∨
              PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB ∨
              PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ∧
            (CorrelationResidual correlationPresent
                (PaperCommonSourceFibers source leftAccess rightAccess
                  readoutA readoutB)
                (PaperDirectRoute routeAdmissible routeStable routeQuotient
                  readoutA readoutB)
                (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                  readoutA readoutB) ↔
              correlationPresent ∧
                ¬ AcceptedCorrelationExplanation
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB)) ∧
              (NonlocalCorrelationResidual correlationPresent localityPackage
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ↔
                CorrelationResidual correlationPresent
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ∧ ¬ localityPackage) := by
  rcases hH with ⟨history⟩
  have hfactor {Q V : Type} (p : H → Q) (t : H → V) :
      PackageClosed p t ↔ ∃ response : Q → V, response ∘ p = t := by
    constructor
    · intro hk
      exact SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Locality.factor_of_fiber_constancy_of_inhabited
        history p t hk
    · rintro ⟨response, hresponse⟩ x y hxy
      exact (congrFun hresponse x).symm.trans
        ((congrArg response hxy).trans (congrFun hresponse y))
  have hA := hfactor (fun h : H => (source h, leftAccess h)) readoutA
  have hB := hfactor (fun h : H => (source h, rightAccess h)) readoutB
  have hI := hfactor
    (interfaceCorrelationQuotient sharedInterface leftAccess rightAccess)
    (jointReadout readoutA readoutB)
  have hR := hfactor routeQuotient (jointReadout readoutA readoutB)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨ha, hb⟩
      rcases hA.mp ha with ⟨responseA, eqA⟩
      rcases hB.mp hb with ⟨responseB, eqB⟩
      exact ⟨responseA, responseB, eqA, eqB⟩
    · rintro ⟨responseA, responseB, eqA, eqB⟩
      exact ⟨hA.mpr ⟨responseA, eqA⟩, hB.mpr ⟨responseB, eqB⟩⟩
  · exact hI
  · constructor
    · rintro ⟨hadmissible, hstable, hfibers⟩
      exact ⟨hadmissible, hstable, hR.mp hfibers⟩
    · rintro ⟨hadmissible, hstable, hfactor⟩
      exact ⟨hadmissible, hstable, hR.mpr hfactor⟩
  · rfl
  · simp only [CorrelationResidual, AcceptedCorrelationExplanation, not_or]
  · rfl

/-- The strengthened F49 bundle without any quotient-surjectivity hypotheses. -/
theorem common_source_nonlocal_correlation_repaired_strengthened_of_nonempty
    {H S I LA LB A B P : Type}
    (source : H → S) (sharedInterface : H → I)
    (leftAccess : H → LA) (rightAccess : H → LB)
    (readoutA : H → A) (readoutB : H → B)
    (routeAdmissible routeStable localityPackage : Prop)
    (routeQuotient : H → P)
    (hH : Nonempty H)
 :
    ((PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB ↔
      ∃ responseA : S × LA → A, ∃ responseB : S × LB → B,
        responseA ∘ (fun h : H => (source h, leftAccess h)) = readoutA ∧
          responseB ∘ (fun h : H => (source h, rightAccess h)) = readoutB) ∧
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess
          readoutA readoutB ↔
        ∃ response : (I × LA) × LB → A × B,
          response ∘ (interfaceCorrelationQuotient sharedInterface
            leftAccess rightAccess) = jointReadout readoutA readoutB) ∧
        (PaperDirectRoute routeAdmissible routeStable routeQuotient
            readoutA readoutB ↔
          routeAdmissible ∧ routeStable ∧
            ∃ response : P → A × B,
              response ∘ routeQuotient = jointReadout readoutA readoutB) ∧
          (AcceptedCorrelationExplanation
              (PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB)
              (PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB)
              (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ↔
            PaperCommonSourceFibers source leftAccess rightAccess
                readoutA readoutB ∨
              PaperDirectRoute routeAdmissible routeStable routeQuotient
                readoutA readoutB ∨
              PaperInterfaceFibers sharedInterface leftAccess rightAccess
                readoutA readoutB) ∧
            (CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
                (PaperCommonSourceFibers source leftAccess rightAccess
                  readoutA readoutB)
                (PaperDirectRoute routeAdmissible routeStable routeQuotient
                  readoutA readoutB)
                (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                  readoutA readoutB) ↔
              (PaperCorrelation leftAccess rightAccess readoutA readoutB) ∧
                ¬ AcceptedCorrelationExplanation
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB)) ∧
              (NonlocalCorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB) localityPackage
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ↔
                CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
                  (PaperCommonSourceFibers source leftAccess rightAccess
                    readoutA readoutB)
                  (PaperDirectRoute routeAdmissible routeStable routeQuotient
                    readoutA readoutB)
                  (PaperInterfaceFibers sharedInterface leftAccess rightAccess
                    readoutA readoutB) ∧ ¬ localityPackage)) ∧
    (∀ (I' : Type) (ι : H → I'),
      ¬ PaperCorrelation leftAccess rightAccess readoutA readoutB →
        PaperInterfaceFibers ι leftAccess rightAccess readoutA readoutB) ∧
    (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB →
      PaperInterfaceFibers source leftAccess rightAccess readoutA readoutB) ∧
    (CorrelationResidual (PaperCorrelation leftAccess rightAccess readoutA readoutB)
      (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB)
      (PaperDirectRoute routeAdmissible routeStable routeQuotient readoutA readoutB)
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB) ↔
    ¬ AcceptedCorrelationExplanation
      (PaperCommonSourceFibers source leftAccess rightAccess readoutA readoutB)
      (PaperDirectRoute routeAdmissible routeStable routeQuotient readoutA readoutB)
      (PaperInterfaceFibers sharedInterface leftAccess rightAccess readoutA readoutB)) := by
  exact ⟨common_source_nonlocal_correlation_repaired_of_nonempty source sharedInterface
    leftAccess rightAccess readoutA readoutB routeAdmissible routeStable
    (PaperCorrelation leftAccess rightAccess readoutA readoutB) localityPackage
    routeQuotient hH,
    fun _ ι hno => no_correlation_interface_fibers ι leftAccess rightAccess
      readoutA readoutB hno,
    common_source_interface_fibers source leftAccess rightAccess readoutA readoutB,
    correlation_residual_iff_not_locally_explainable source sharedInterface
      leftAccess rightAccess readoutA readoutB routeAdmissible routeStable routeQuotient⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.CommonSourceNonlocal
