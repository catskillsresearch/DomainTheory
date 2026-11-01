
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

class Isolated (x : Pomega) : Prop where
  out : ∃ n, x = e n

end DomainTheory.DataTypesAsLattices
