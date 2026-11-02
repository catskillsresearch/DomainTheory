
module

public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
import Mathlib.Tactic.Finiteness.Attr
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

end DomainTheory.DataTypesAsLattices
