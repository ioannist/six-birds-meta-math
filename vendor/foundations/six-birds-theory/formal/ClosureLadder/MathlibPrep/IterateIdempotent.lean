import ClosureLadder.MathlibPrep.FunctionIdempotent

/-!
# Iteration lemmas for idempotent functions
-/

namespace Function.Idempotent

def Iterate {α : Type u} (f : α → α) : Nat → α → α
  | 0 => fun x => x
  | n + 1 => fun x => Iterate f n (f x)

/-- If `f` is idempotent, all positive iterates of `f` agree with one application. -/
theorem iterate_succ_apply {α : Type u} {f : α → α} (hf : Function.Idempotent f)
    (n : Nat) (x : α) :
    Iterate f (n + 1) x = f x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      calc
        Iterate f (n + 2) x = Iterate f (n + 1) (f x) := by
          rfl
        _ = f (f x) := by
          exact ih (f x)
        _ = f x := hf x

/-- If `f` is idempotent, any iterate with `1 ≤ n` equals a single application. -/
theorem iterate_apply_eq {α : Type u} {f : α → α} (hf : Function.Idempotent f)
    {n : Nat} (hn : 1 ≤ n) (x : α) :
    Iterate f n x = f x := by
  cases n with
  | zero =>
      cases hn
  | succ n =>
      exact iterate_succ_apply hf n x

end Function.Idempotent
