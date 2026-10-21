/-ai
Unfolding the fold of an element of the sum-and-product system returns that element.

The two carriers are compared by antisymmetry. A token of the composite carrier is the unfold of a token already in the original element. Conversely, each token of the original element is the unfold of its fold, and that fold lies in the folded element because unfolding it returns the original token.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.treeUnfold_treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

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
