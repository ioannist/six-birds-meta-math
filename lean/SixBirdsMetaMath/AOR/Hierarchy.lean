import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.AOR.Refinement

namespace SixBirdsMetaMath.AOR.Hierarchy

/-!
This retained adapter is synchronized with the maintained Needles version.
References below to semantic AOR modules absent from this namespace mean
`SixBirdsNeedles.AOR.*`; this module does not re-export those endpoints.

Legacy hierarchy name retained for paper traceability. The literal original
empty-defect definition cannot have the claimed strict second inclusion; see
`LiteralHierarchy.no_strict_cascade_witness`. The revised operational hierarchy
is proved in `OperationalHierarchy.strict_hierarchy`, using persistent records,
actual operation traces, finite recovery and uniform quantitative control.
Its quantifiers differ explicitly from the original all-refinement assertion.
-/

end SixBirdsMetaMath.AOR.Hierarchy
