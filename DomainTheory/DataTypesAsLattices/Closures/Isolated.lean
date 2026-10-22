
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Isolated (compact) elements of `Pω` are the finite sets `e n`. -/
class Isolated (x : Pomega) : Prop where
  out : ∃ n, x = e n

end DomainTheory.DataTypesAsLattices
