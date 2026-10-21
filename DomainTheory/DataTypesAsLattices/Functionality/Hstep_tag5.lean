/-ai
The interpreter step at a tag-five injection of an element equals the application clause at that same tagged expression.

Unfold the step and the expression tag. Definite conditionals at positive numerals take the second branch. Three predecessors of five are two and four predecessors of five are one, the predecessor of one is zero, and the conditional at zero selects the application clause.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
















































theorem Hstep_tag5 (H x t : Pomega) :
    Hstep H (tagInj 5 x) t = hApp H (tagInj 5 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
    predSet_iterate_ofNat (k := 4) (i := 1),
    predSet_iterate_self, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
