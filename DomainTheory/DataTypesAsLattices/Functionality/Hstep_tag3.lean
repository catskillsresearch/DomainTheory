/-ai
The interpreter step at a tag-three injection of an element equals the predecessor clause at that same tagged expression.

Unfold the step and the expression tag. Definite conditionals at positive numerals take the second branch. Three predecessors of the numeral three are zero, and the conditional at zero selects the predecessor clause.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag3 (H x t : Pomega) :
    Hstep H (tagInj 3 x) t = hPred H (tagInj 3 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_self,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
