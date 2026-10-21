/-ai
Unfolding tree tokens induces an order isomorphism between the elements of the tree system and the elements of the sum of the original system with the product of the tree system with itself. The forward map unfolds an element and the inverse folds one; the two round trips are the corresponding element identities. One tree element lies below another exactly when its unfold does, because a token of the first unfolds into the second precisely when the token itself lies in the second, using that folding after unfolding restores the token.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement
public import DomainTheory.BridgeTheorems.unfoldElement_foldElement
public import DomainTheory.BridgeTheorems.foldElement_unfoldElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- **Factoid 8.1 at domain level.** `|T| ≃o |A + (T × T)|` via `treeUnfold`. -/
def treeDomainIso : (treeSystem A).Element ≃o (treeRhs A).Element where
  toFun := unfoldElement A
  invFun := foldElement A
  left_inv := foldElement_unfoldElement A
  right_inv := unfoldElement_foldElement A
  map_rel_iff' := by
    intro x₁ x₂
    constructor
    · intro h t ht
      have : treeUnfold A t ∈ (unfoldElement A x₁).carrier := ⟨t, ht, rfl⟩
      have : treeUnfold A t ∈ (unfoldElement A x₂).carrier := h this
      have : t ∈ (foldElement A (unfoldElement A x₂)).carrier := this
      rwa [foldElement_unfoldElement] at this
    · intro h s hs
      rcases hs with ⟨t, ht, rfl⟩
      exact ⟨t, h ht, rfl⟩

end DomainTheory.BridgeTheorems
