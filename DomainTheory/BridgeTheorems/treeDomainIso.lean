module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement
public import DomainTheory.BridgeTheorems.unfoldElement_foldElement
public import DomainTheory.BridgeTheorems.foldElement_unfoldElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

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
