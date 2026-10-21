/-ai
For every natural number n, the conditional set of the numeral n + 1, with branches x and y, equals y.

Membership extensionality and the definitions of the conditional set and of the numeral give the equality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



theorem condSet_ofNat_succ (n : ℕ) (x y : Pomega) :
    condSet (ofNat (n + 1)) x y = y := by
  ext k
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
