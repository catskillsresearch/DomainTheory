module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.foldFinset
public import DomainTheory.BridgeTheorems.mem_foldr_fold

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_foldFinset
    {Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))}
    {t : TreeToken α} :
    t ∈ foldFinset A Y ↔ ∃ s ∈ Y, treeFold A s = t := by
  unfold foldFinset
  rw [mem_foldr_fold]
  simp only [Finset.mem_def]

end DomainTheory.BridgeTheorems
