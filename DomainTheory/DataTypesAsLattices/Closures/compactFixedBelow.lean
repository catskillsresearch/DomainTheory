module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Compact fixed points below `x`: the isolated points `a(e n)` contained in `x`. -/
def compactFixedBelow (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {k | (∃ n, (k : Pomega) = funOf a (e n)) ∧ (k : Pomega) ⊆ (x : Pomega)}

end DomainTheory.DataTypesAsLattices
