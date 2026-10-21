/-ai
The doubly strict conditional on ⊤ is ⊤.

Both sides agree by unfolding the doubly strict conditional, the McCarthy conditional, and ⊤.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dcondSet_top (x y : Pomega) : dcondSet topElem x y = topElem := by
  ext n
  simp [dcondSet, condSet, topElem]

end DomainTheory.DataTypesAsLattices
