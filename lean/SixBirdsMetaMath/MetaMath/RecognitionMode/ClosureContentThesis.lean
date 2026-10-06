import SixBirdsMetaMath.MetaMath.RecognitionMode.Template

namespace SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis

open SixBirdsMetaMath.MetaMath.RecognitionMode.Template

/-!
T9 Closure-Content Thesis.

This module records the recognition-mode claim that the load-bearing
structural source for TSO-column closures is formed-layer closure content,
not something separately derived from current framework primitives.
-/

/-- Load-bearing structural content needed for target closure. -/
structure StructuralContent where
  formedLayerContentOf : FormedClosure → Prop
  derivableFromFrameworkPrimitives : Prop
  namedAcceptedSourceFor : FormedClosure → Prop
  deriving Inhabited

/--
Load-bearing structural content for closure `c` targeting `X`.
Opaque so the conditional schema genuinely asserts the M5 closure-content
thesis rather than reducing from the definition.
-/
opaque loadBearingFor (c : FormedClosure) (X : Prop) : StructuralContent

/-- `s` is content of formed-layer closure per Foundations I for `c`. -/
def IsFormedLayerClosureContent (s : StructuralContent) (c : FormedClosure) : Prop :=
  s.formedLayerContentOf c

/-- `s` is separately derivable from currently available framework primitives. -/
def IsDerivableFromFrameworkPrimitives (s : StructuralContent) : Prop :=
  s.derivableFromFrameworkPrimitives

/-- The recognition-mode landing names `s` explicitly as accepted source for `c`. -/
def NamedAsAcceptedSource (s : StructuralContent) (c : FormedClosure) : Prop :=
  s.namedAcceptedSourceFor c

/--
T9 obligation: for TSO-column closures, the load-bearing structural content
is formed-layer closure content, is not separately derivable from current
framework primitives, and is named explicitly as accepted source.
-/
def ClosureContentThesisSchema : Prop :=
  ∀
    (c : FormedClosure) (X : Prop)
    (_hcolumn : VDifferentialTSOColumn c),
    IsFormedLayerClosureContent (loadBearingFor c X) c ∧
    ¬ IsDerivableFromFrameworkPrimitives (loadBearingFor c X) ∧
    NamedAsAcceptedSource (loadBearingFor c X) c

/-- Conditional application of the explicit schema hypothesis. -/
theorem closure_content_thesis
    (hschema : ClosureContentThesisSchema)
    (c : FormedClosure) (X : Prop)
    (hcolumn : VDifferentialTSOColumn c) :
    IsFormedLayerClosureContent (loadBearingFor c X) c ∧
    ¬ IsDerivableFromFrameworkPrimitives (loadBearingFor c X) ∧
    NamedAsAcceptedSource (loadBearingFor c X) c :=
  hschema c X hcolumn

end SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis
