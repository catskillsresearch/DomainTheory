/-ai
The self-application of a set d equals the union, over finite sets contained in d, of the self-applications of those finite sets.

This is the diagonal case of Theorem 1.3 for application, using Scott continuity of application in the function argument and in the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Appendix calculation: `d(d) = ⋃ { e_l(e_l) | e_l ⊆ d }`. -/
theorem funOf_diag_iUnion (d : Pomega) :
    funOf d d = ⋃ l, {m | e l ⊆ d ∧ m ∈ funOf (e l) (e l)} := by
  have h := theorem_1_3_diag (x := d)
    (f := fun u y => funOf u y)
    (fun y => funOf_isScottContinuous_left y)
    (fun u => funOf_isScottContinuous u)
  exact h

end DomainTheory.DataTypesAsLattices
