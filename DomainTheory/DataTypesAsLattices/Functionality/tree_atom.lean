
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inl
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_38
public import DomainTheory.DataTypesAsLattices.Functionality.typed_bot_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, after (4.38).** The atom `⟨0⟩ : tree`. -/
theorem tree_atom : typed (pairSeq (ofNat 0) botElem) treeR := by
  rw [eq_4_38]
  exact plusR_typed_inl typed_bot_bot

end DomainTheory.DataTypesAsLattices
