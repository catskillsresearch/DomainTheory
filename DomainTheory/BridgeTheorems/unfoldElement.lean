/-ai
The map unfoldElement sends a tree-system element to the element of the sum-and-product system whose carrier is the image of the tree carrier under tree unfolding. A finite set of sum tokens is consistent because its fold lies in the tree element, tree consistency of that fold transports to sum consistency of the unfold, and unfolding after folding restores the set. If the set entails a sum token, the fold of the set entails the fold of the token, so the tree element contains that fold, and unfolding it recovers the token.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.TreeProd
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.treeUnfold_treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.foldFinset
public import DomainTheory.BridgeTheorems.mem_foldFinset
public import DomainTheory.BridgeTheorems.unfoldFinset_foldFinset
public import DomainTheory.BridgeTheorems.TreeCon_image_sumCon
public import DomainTheory.BridgeTheorems.SumEnt_treeFold
public import DomainTheory.BridgeTheorems.saturated_of_closed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Image of a tree element under `treeUnfold` is an official RHS element. -/
def unfoldElement (x : (treeSystem A).Element) : (treeRhs A).Element where
  carrier := treeUnfold A '' x.carrier
  consistent := by
    intro Y hY
    have hFold : ↑(foldFinset A Y) ⊆ x.carrier := by
      intro t ht
      rcases (mem_foldFinset A).1 (Finset.mem_coe.1 ht) with ⟨s, hs, rfl⟩
      have hs' : s ∈ treeUnfold A '' x.carrier := hY (Finset.mem_coe.2 hs)
      rcases hs' with ⟨t', ht', hU⟩
      have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
      rwa [hU] at this
    have hCon : TreeCon A (foldFinset A Y) := x.consistent _ hFold
    have : SumCon A (TreeProd A) (unfoldFinset A (foldFinset A Y)) :=
      TreeCon_image_sumCon A hCon
    rwa [unfoldFinset_foldFinset] at this
  closed := by
    intro Y s hY hEnt
    have hFold : ↑(foldFinset A Y) ⊆ x.carrier := by
      intro t ht
      rcases (mem_foldFinset A).1 (Finset.mem_coe.1 ht) with ⟨s', hs', rfl⟩
      have hs'' : s' ∈ treeUnfold A '' x.carrier := hY (Finset.mem_coe.2 hs')
      rcases hs'' with ⟨t', ht', hU⟩
      have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
      rwa [hU] at this
    have hEnt' : SumEnt A (TreeProd A)
        (unfoldFinset A (foldFinset A Y)) s := by
      rwa [unfoldFinset_foldFinset]
    have hT : TreeEnt A (foldFinset A Y) (treeFold A s) :=
      SumEnt_treeFold A hEnt'
    have ht : treeFold A s ∈ x.carrier :=
      x.closed _ _ hFold hT
    refine ⟨treeFold A s, ht, treeUnfold_treeFold A s⟩

end DomainTheory.BridgeTheorems
