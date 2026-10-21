/-ai
The doubly strict conditional on the numeral 1 returns its right argument.

Both sides agree by unfolding the doubly strict conditional, the McCarthy conditional, the numeral, and ⊤.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_ofNat_one (x y : Pomega) : dcondSet (ofNat 1) x y = y := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

end DomainTheory.DataTypesAsLattices
