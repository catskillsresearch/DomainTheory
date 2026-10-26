module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.retractBasis_eq_compactFixedBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem fixed_eq_sSup_compacts {a : Pomega} (ha : Closure a)
    (x : Fixpoints (funOf a)) :
    DirectedSet (compactFixedBelow a x) ∧
      x = sSup (compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact ⟨retractBasis.directed ha.out.2 x, retractBasis.eq_sSup ha.out.2 x⟩

end DomainTheory.DataTypesAsLattices
