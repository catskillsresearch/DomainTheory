/-ai
Scott 1976, Theorem 4.3 (ii). If a set is typed by the function space a ∘→ b and an argument is typed by a, then the value is typed by b.

Typing and the function-space application law write the set as the composite of b with the composite of the set and a. Applying that equation and unfolding composition twice writes the value as b applied after the set applied after a. Typing of the argument replaces the inner application of a by the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































/-- **Scott 1976, Theorem 4.3 (ii).** `u : a ∘→ b` means `u` is restricted
to `a` and takes values in `b`. -/
theorem theorem_4_3_ii {a b u x : Pomega}
    (hu : typed u (arrowR a b)) (hx : typed x a) :
    typed (funOf u x) b := by
  have hu' : u = comp b (comp u a) := by
    simpa [typed, arrowR_app] using hu
  have : funOf u x = funOf b (funOf u (funOf a x)) := by
    have h1 : funOf u x = funOf (comp b (comp u a)) x :=
      congrArg (fun w => funOf w x) hu'
    rw [h1, comp_app, comp_app]
  rwa [show funOf a x = x from hx.symm] at this

end DomainTheory.DataTypesAsLattices
