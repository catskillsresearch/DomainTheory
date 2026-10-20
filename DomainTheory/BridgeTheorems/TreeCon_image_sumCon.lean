/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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

set_option linter.unusedSectionVars false

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
