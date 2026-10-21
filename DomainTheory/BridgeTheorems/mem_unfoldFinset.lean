/-ai
A sum token lies in the unfold of a finite set of tree tokens if and only if it is the tree unfold of some member of that set.

Unfold the definition of the unfolded finset and apply the membership rule for the multiset fold of the unfold insertion, rewritten along finset membership.
ai-/
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
