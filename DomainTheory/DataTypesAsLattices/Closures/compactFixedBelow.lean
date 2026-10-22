module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Compact fixed points below `x`: the isolated points `a(e n)` contained in `x`. -/
def compactFixedBelow (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {k | (∃ n, (k : Pomega) = funOf a (e n)) ∧ (k : Pomega) ⊆ (x : Pomega)}

end DomainTheory.DataTypesAsLattices
