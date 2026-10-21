/-ai
For every list of natural numbers, the union of its numerals is combinatory.

The empty union is bottom, which is combinatory. The union of a head with the union of the tail is combinatory because binary union preserves the combinatory property, the numeral of the head is combinatory, and the tail is combinatory by induction.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.union_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

























































theorem unionBits_combinatory : ∀ ks, IsCombinatory (unionBits ks)
  | [] => bot_combinatory
  | k :: ks => union_combinatory (ofNat_combinatory k) (unionBits_combinatory ks)

end DomainTheory.DataTypesAsLattices
