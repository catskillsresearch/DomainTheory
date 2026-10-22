/-ai
Scott's theorem on the universe operator says that, on a closure, the operator agrees with the closure on every argument and is idempotent on those values.

The agreement is the equation that the universe operator fixes closures on values, and the idempotence is the corresponding idempotence equation.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_17
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_eq

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.5 / (5.18).** `V` fixes closures on values. -/
theorem theorem_5_5 {a : Pomega} (ha : Closure a) (x : Pomega) :
    Vapply a x = funOf a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_18_eq ha x, eq_5_17 a x⟩

end DomainTheory.DataTypesAsLattices
