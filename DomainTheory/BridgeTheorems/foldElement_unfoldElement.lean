/-ai
Folding the unfolding of a tree element returns the original element.

The two carriers are compared by antisymmetry. A token in the fold is the fold of the unfolding of some token of the original element, and closure saturates the element under folding after unfolding, so the fold of the unfolding of the token lies in the element. That fold is either the token itself or, when the token is one of the two product-bottom encodings, the other encoding, in which case closure under those two bottom pair tokens puts the token in the element. Conversely, every token of the element is the fold of its own unfolding.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.treeFold_eq_or_pairBots
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.mem_closed_pair_bots
public import DomainTheory.BridgeTheorems.saturated_of_closed
public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem foldElement_unfoldElement (x : (treeSystem A).Element) :
    foldElement A (unfoldElement A x) = x := by
  refine le_antisymm ?_ ?_
  · intro t ht
    rcases ht with ⟨t', ht', hU⟩
    have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
    have hft : treeFold A (treeUnfold A t) ∈ x.carrier := by
      rwa [hU] at this
    rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
    · rwa [h] at hft
    · exact (mem_closed_pair_bots A x).1 (by rwa [hf] at hft)
  · intro t ht
    exact ⟨t, ht, rfl⟩

end DomainTheory.BridgeTheorems
