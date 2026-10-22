module

public import Mathlib.Order.Hom.Basic
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

theorem SumCon_image_treeCon {u : Finset (TreeToken α)}
    (hu : SumCon A (TreeProd A) (unfoldFinset A u)) : TreeCon A u := by
  rcases hu with ⟨hL, hr⟩ | ⟨hl, hR⟩
  · refine TreeCon.left _ (by rwa [lftFinset_image_unfold] at hL) ?_ ?_
    · ext t
      constructor
      · intro ht
        have : (⟨(t, treeBot), ⟨Or.inr rfl⟩⟩ : ProdToken (treeSystem A) (treeSystem A)) ∈
            rhtFinset (unfoldFinset A u) :=
          (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨t, mem_pairLFinset.1 ht, rfl⟩)
        rw [hr] at this
        exact False.elim (Finset.notMem_empty _ this)
      · intro ht
        exact False.elim (Finset.notMem_empty t ht)
    · ext t
      constructor
      · intro ht
        have : (⟨(treeBot, t), ⟨Or.inl rfl⟩⟩ : ProdToken (treeSystem A) (treeSystem A)) ∈
            rhtFinset (unfoldFinset A u) :=
          (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨t, mem_pairRFinset.1 ht, rfl⟩)
        rw [hr] at this
        exact False.elim (Finset.notMem_empty _ this)
      · intro ht
        exact False.elim (Finset.notMem_empty t ht)
  · refine TreeCon.right _ (by rwa [lftFinset_image_unfold] at hl) ?_ ?_
    · have hsub : pairLFinset u ⊆
          fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro t ht
        exact (mem_fstFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(t, treeBot), ⟨Or.inr rfl⟩⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨t, mem_pairLFinset.1 ht, rfl⟩),
            rfl, rfl⟩
      exact (treeSystem A).con_subset hR.1 hsub
    · have hsub : pairRFinset u ⊆
          sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro t ht
        exact (mem_sndFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(treeBot, t), ⟨Or.inl rfl⟩⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨t, mem_pairRFinset.1 ht, rfl⟩),
            rfl, rfl⟩
      exact (treeSystem A).con_subset hR.2 hsub

end DomainTheory.BridgeTheorems
