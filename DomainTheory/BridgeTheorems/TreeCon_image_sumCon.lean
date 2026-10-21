/-ai
If a finite set of tree tokens is consistent, then its unfolding is consistent in the sum of the original system and the product of the tree system with itself.

Tree consistency is a left case or a right case. In the left case the atoms are consistent and both pair projections are empty. The left part of the unfolding is the atom set, and the right part is empty because a right-hand product token would come from a pair-left or pair-right token. In the right case the atoms are empty and both pair projections are consistent. The left part of the unfolding is empty. The first projection of the right part sits inside the pair-left set with bottom inserted, because a first component comes from a pair-left token or from the bottom first component of a pair-right token, and consistency passes to this subset. The second projection sits inside the pair-right set with bottom inserted in the same way.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.TreeProd
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.lftFinset_image_unfold
public import DomainTheory.BridgeTheorems.rhtFinset_image_unfold_mem

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem TreeCon_image_sumCon {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    SumCon A (TreeProd A) (unfoldFinset A u) := by
  cases hu with
  | left _ hA hL hR =>
    refine Or.inl ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact hA
    · ext y
      constructor
      · intro hy
        rcases (rhtFinset_image_unfold_mem A u y).1 hy with ⟨t, ht, _⟩ | ⟨t, ht, _⟩
        · exact False.elim (Finset.notMem_empty t (hL ▸ mem_pairLFinset.2 ht))
        · exact False.elim (Finset.notMem_empty t (hR ▸ mem_pairRFinset.2 ht))
      · intro hy
        exact False.elim (Finset.notMem_empty y hy)
  | right _ hA hL hR =>
    refine Or.inr ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact hA
    · refine ⟨?_, ?_⟩
      · -- fst of the product tokens is a TreeCon set (pairL, plus bot if needed)
        have hsub :
            fstFinset (treeSystem A) (treeSystem A)
                (rhtFinset (unfoldFinset A u)) ⊆
              insert .bot (pairLFinset u) := by
          intro t ht
          rcases (mem_fstFinset (treeSystem A) (treeSystem A)).1 ht with ⟨p, hp, hb, rfl⟩
          rcases (rhtFinset_image_unfold_mem A u p).1 hp with ⟨s, hs, hp'⟩ | ⟨s, hs, hp'⟩
          · subst hp'
            exact Finset.mem_insert_of_mem (mem_pairLFinset.2 hs)
          · subst hp'
            exact Finset.mem_insert_self _ _
        exact (treeSystem A).con_subset (TreeCon_insert_bot A hL) hsub
      · have hsub :
            sndFinset (treeSystem A) (treeSystem A)
                (rhtFinset (unfoldFinset A u)) ⊆
              insert .bot (pairRFinset u) := by
          intro t ht
          rcases (mem_sndFinset (treeSystem A) (treeSystem A)).1 ht with ⟨p, hp, ha, rfl⟩
          rcases (rhtFinset_image_unfold_mem A u p).1 hp with ⟨s, hs, hp'⟩ | ⟨s, hs, hp'⟩
          · subst hp'
            exact Finset.mem_insert_self _ _
          · subst hp'
            exact Finset.mem_insert_of_mem (mem_pairRFinset.2 hs)
        exact (treeSystem A).con_subset (TreeCon_insert_bot A hR) hsub

end DomainTheory.BridgeTheorems
