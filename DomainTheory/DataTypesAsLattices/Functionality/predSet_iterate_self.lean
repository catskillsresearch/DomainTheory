/-ai
The k-fold predecessor of the numeral k is the numeral 0.

This is the iteration law for the predecessor on numerals, taken at the second argument 0.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem predSet_iterate_self (k : ℕ) :
    predSet^[k] (ofNat k) = ofNat 0 := by
  simpa using predSet_iterate_ofNat k 0

end DomainTheory.DataTypesAsLattices
