/-!
# Idempotent functions
-/

namespace Function

/-- A unary function is idempotent if applying it twice is the same as applying it once. -/
def Idempotent (f : α → α) : Prop := ∀ x, f (f x) = f x

end Function
