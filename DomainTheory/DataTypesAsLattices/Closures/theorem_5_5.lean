module

public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
import DomainTheory.DataTypesAsLattices.Closures.eq_5_18
import DomainTheory.DataTypesAsLattices.Closures.eq_5_17

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_5 {a : Pomega} (ha : Closure a) (x : Pomega) :
    Vapply a x = funOf a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_18.eq ha x, eq_5_17 a x⟩

end DomainTheory.DataTypesAsLattices
