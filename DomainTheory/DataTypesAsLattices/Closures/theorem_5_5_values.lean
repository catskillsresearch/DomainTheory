module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_17

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.5 (partial).** `V(a)` is always a closure of `x`,
and `V` fixes exactly the closure operations in the sense of (5.18) on values. -/
theorem theorem_5_5_values (a x : Pomega) :
    x ⊆ Vapply a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_16 a x, eq_5_17 a x⟩

end DomainTheory.DataTypesAsLattices
