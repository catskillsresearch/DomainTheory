/-ai
Scott's discussion after equation (4.38) states that if x and y are typed by the tree retract, then the pair of the numeral 1 with the pair of x and y is typed by the tree retract.

Rewrite by equation (4.38). The right typing rule for the sum applies once the tensor typing says that the inner pair is typed by the tensor product of the tree retract with itself.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inr
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_38

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, after (4.38).** Binary trees are in `tree`. -/
theorem tree_node {x y : Pomega} (hx : typed x treeR) (hy : typed y treeR) :
    typed (pairSeq (ofNat 1) (pairSeq x y)) treeR := by
  rw [eq_4_38]
  exact plusR_typed_inr ((typed_pairSeq_tensorR treeR treeR x y).mpr ⟨hx, hy⟩)

end DomainTheory.DataTypesAsLattices
