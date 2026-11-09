module

public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.mem_foldr_unfold

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_unfoldFinset {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))} :
    s ∈ unfoldFinset A u ↔ ∃ t ∈ u, treeUnfold A t = s := by
  unfold unfoldFinset
  rw [mem_foldr_unfold]
  simp only [Finset.mem_def]

end DomainTheory.BridgeTheorems
