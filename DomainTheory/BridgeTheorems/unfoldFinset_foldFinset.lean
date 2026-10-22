/-ai
Unfolding the fold of a finite set of sum tokens returns that set.

By extensionality, a sum token in the composite is the unfold of a tree token that is the fold of some member, and unfolding after folding restores that member. Conversely, the fold of a member unfolds back to the member, so the member lies in the composite.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.treeUnfold_treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.mem_unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.foldFinset
public import DomainTheory.BridgeTheorems.mem_foldFinset

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem unfoldFinset_foldFinset
    (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    unfoldFinset A (foldFinset A Y) = Y := by
  ext s
  constructor
  · intro hs
    rcases (mem_unfoldFinset A).1 hs with ⟨t, ht, hU⟩
    rcases (mem_foldFinset A).1 ht with ⟨s', hs', rfl⟩
    rw [treeUnfold_treeFold] at hU
    rwa [← hU]
  · intro hs
    exact (mem_unfoldFinset A).2 ⟨treeFold A s,
      (mem_foldFinset A).2 ⟨s, hs, rfl⟩, treeUnfold_treeFold A s⟩

end DomainTheory.BridgeTheorems
