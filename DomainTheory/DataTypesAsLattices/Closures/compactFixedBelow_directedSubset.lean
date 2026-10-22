module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem compactFixedBelow_directedSubset {a : Pomega} (ha : Closure a)
    (x : Fixpoints (funOf a)) :
    DirectedSubset (compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact retractBasis_directedSubset ha.out.2 x

end DomainTheory.DataTypesAsLattices
