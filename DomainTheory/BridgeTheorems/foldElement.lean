module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.TreeProd
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.mem_unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.SumCon_image_treeCon
public import DomainTheory.BridgeTheorems.TreeEnt_sumEnt

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Preimage of an official RHS element under `treeUnfold` is a tree element. -/
def foldElement (y : (treeRhs A).Element) : (treeSystem A).Element where
  carrier := treeUnfold A ⁻¹' y.carrier
  consistent := by
    intro Y hY
    have him : ↑(unfoldFinset A Y) ⊆ y.carrier := by
      intro s hs
      rcases (mem_unfoldFinset A).1 (Finset.mem_coe.1 hs) with ⟨t, ht, rfl⟩
      exact hY (Finset.mem_coe.2 ht)
    have : SumCon A (TreeProd A) (unfoldFinset A Y) := y.consistent _ him
    exact SumCon_image_treeCon A this
  closed := by
    intro Y p hY hEnt
    have him : ↑(unfoldFinset A Y) ⊆ y.carrier := by
      intro s hs
      rcases (mem_unfoldFinset A).1 (Finset.mem_coe.1 hs) with ⟨t, ht, rfl⟩
      exact hY (Finset.mem_coe.2 ht)
    have hS : SumEnt A (TreeProd A) (unfoldFinset A Y) (treeUnfold A p) :=
      TreeEnt_sumEnt A hEnt
    exact y.closed _ _ him hS

end DomainTheory.BridgeTheorems
