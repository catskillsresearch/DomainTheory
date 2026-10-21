/-ai
The McCarthy conditional on the numeral 0 returns its left argument.

Unfolding the conditional and the numeral leaves only the left branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eq_2_7_zero (x y : Pomega) : condSet (ofNat 0) x y = x := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
