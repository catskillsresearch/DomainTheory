module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















theorem compactFixedBelow_directedSubset {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSubset (compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact retractBasis_directedSubset ha.2 x

end DomainTheory.DataTypesAsLattices
