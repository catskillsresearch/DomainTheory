module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.mem_foldr_unfold

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_unfoldFinset {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))} :
    s ∈ unfoldFinset A u ↔ ∃ t ∈ u, treeUnfold A t = s := by
  unfold unfoldFinset
  rw [mem_foldr_unfold]
  simp only [Finset.mem_def]

end DomainTheory.BridgeTheorems
