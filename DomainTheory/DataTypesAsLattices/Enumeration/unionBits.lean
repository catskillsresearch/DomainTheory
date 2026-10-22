/-ai
The union of a list of natural numbers is bottom when the list is empty, and otherwise the union of the numeral of the head with the union of the tail.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def unionBits : List ℕ → Pomega
  | [] => botElem
  | k :: ks => ofNat k ∪ unionBits ks

end DomainTheory.DataTypesAsLattices
