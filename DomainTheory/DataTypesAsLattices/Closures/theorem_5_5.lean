module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_17
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_eq

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.5 / (5.18).** `V` fixes closures on values. -/
theorem theorem_5_5 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x = funOf a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_18_eq ha x, eq_5_17 a x⟩

end DomainTheory.DataTypesAsLattices
