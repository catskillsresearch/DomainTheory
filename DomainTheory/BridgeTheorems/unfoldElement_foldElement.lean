module

public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement
public import DomainTheory.BridgeTheorems.treeUnfold_treeFold

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem unfoldElement_foldElement (y : (treeRhs A).Element) :
    unfoldElement A (foldElement A y) = y := by
  refine le_antisymm ?_ ?_
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact ht
  · intro s hs
    refine ⟨treeFold A s, ?_, treeUnfold_treeFold A s⟩
    change treeUnfold A (treeFold A s) ∈ y.carrier
    rwa [treeUnfold_treeFold]

end DomainTheory.BridgeTheorems
