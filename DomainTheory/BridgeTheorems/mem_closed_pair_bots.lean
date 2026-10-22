/-ai
A tree-system element contains the token pair-left of bottom if and only if it contains pair-right of bottom.

If pair-left of bottom lies in the carrier, its singleton is contained in the carrier, and the entailment of pair-right of bottom from that singleton is absorbed by closure. The converse absorbs the entailment of pair-left of bottom from the singleton of pair-right of bottom in the same way.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.TreeEnt_pairL_bot_of_pairs
public import DomainTheory.BridgeTheorems.TreeEnt_pairR_bot_of_pairs

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_closed_pair_bots (x : (treeSystem A).Element) :
    .pairL .bot ∈ x.carrier ↔ .pairR .bot ∈ x.carrier := by
  constructor
  · intro h
    have hsub : (({TreeToken.pairL treeBot} : Finset (TreeToken α)) : Set _) ⊆
        x.carrier := by
      intro a ha
      have : a = .pairL treeBot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
      subst this; exact h
    exact x.closed {TreeToken.pairL treeBot} (.pairR treeBot) hsub
      (TreeEnt_pairR_bot_of_pairs A (x.consistent _ hsub)
        (Or.inl (Finset.ne_empty_of_mem (by
          rw [pairLFinset_singleton_pairL]; exact Finset.mem_singleton_self _))))
  · intro h
    have hsub : (({TreeToken.pairR treeBot} : Finset (TreeToken α)) : Set _) ⊆
        x.carrier := by
      intro a ha
      have : a = .pairR treeBot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
      subst this; exact h
    exact x.closed {TreeToken.pairR treeBot} (.pairL treeBot) hsub
      (TreeEnt_pairL_bot_of_pairs A (x.consistent _ hsub)
        (Or.inr (Finset.ne_empty_of_mem (by
          rw [pairRFinset_singleton_pairR]; exact Finset.mem_singleton_self _))))

end DomainTheory.BridgeTheorems
