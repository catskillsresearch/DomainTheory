
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.treeR
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
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
