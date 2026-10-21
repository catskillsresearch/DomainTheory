/-ai
The union of the numerals of a list of natural numbers equals the set of entries of that list.

The empty union is bottom, which is empty. For a nonempty list, extensionality and the inductive equation reduce membership to membership of the head numeral or membership in the tail.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

























































theorem unionBits_eq : ∀ ks : List ℕ, unionBits ks = {n | n ∈ ks}
  | [] => by simp [unionBits, botElem]
  | k :: ks => by
    ext n
    simp [unionBits, unionBits_eq ks, ofNat]

end DomainTheory.DataTypesAsLattices
