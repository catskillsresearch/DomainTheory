/-ai
If a finite set of tree tokens entails a tree token, then the unfolding of the set entails the unfolding of the token in the sum of the original system and the product of the tree system with itself.

Consistency of the tree set gives sum consistency of the unfolding. A bottom token has a trivial payload. An atom token has its atom-consistency and its atom-entailment transported across the identification of the left part of the unfolding with the atom set. For a pair-left token the right part of the unfolding is nonempty, because the payload supplies either a pair-left token, unfolding to a product with bottom on the right, or a pair-right token, unfolding to a product with bottom on the left. The product of the two tree systems is then consistent. Its first projection contains the pair-left set and is consistent, and the pair-left payload transports along that inclusion, or is entailment of bottom when the component is bottom. Its second projection is consistent and entails bottom. For a pair-right token the right part is likewise nonempty, the first projection entails bottom, and the second projection contains the pair-right set, so the pair-right payload transports along that inclusion, or is entailment of bottom when the component is bottom.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.TreeProd
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.lftFinset_image_unfold
public import DomainTheory.BridgeTheorems.rhtFinset_image_unfold_mem
public import DomainTheory.BridgeTheorems.TreeCon_image_sumCon

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem TreeEnt_sumEnt {u : Finset (TreeToken α)} {p : TreeToken α}
    (h : TreeEnt A u p) :
    SumEnt A (TreeProd A) (unfoldFinset A u) (treeUnfold A p) := by
  have hCon : SumCon A (TreeProd A) (unfoldFinset A u) :=
    TreeCon_image_sumCon A h.1
  refine ⟨hCon, ?_⟩
  cases p with
  | bot => exact trivial
  | atom x =>
    refine ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact h.2.1
    · rw [lftFinset_image_unfold]; exact h.2.2
  | pairL t =>
    have hr : rhtFinset (unfoldFinset A u) ≠ ∅ := by
      rcases h.2.2.2.2 with ⟨hne, _⟩ | ⟨_, hR⟩
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩))
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hR
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩))
    refine ⟨hr, ?_⟩
    refine ⟨hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2), ?_, ?_⟩
    · intro
      -- T.Ent fst t
      have hsub : pairLFinset u ⊆
          fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro s hs
        exact (mem_fstFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(s, treeBot), ⟨Or.inr rfl⟩⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩),
            rfl, rfl⟩
      have hFstCon : fstFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.1)
      rcases h.2.2.2.2 with ⟨hne, hPay⟩ | ⟨rfl, _⟩
      · exact (treeSystem A).ent_trans hFstCon h.2.2.1
          (fun y hy => (treeSystem A).ent_refl hFstCon (hsub hy)) ⟨h.2.2.1, hPay⟩
      · exact (treeSystem A).ent_bot hFstCon
    · intro ht
      have hSndCon : sndFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.2)
      exact (treeSystem A).ent_bot hSndCon

  | pairR t =>
    have hr : rhtFinset (unfoldFinset A u) ≠ ∅ := by
      rcases h.2.2.2.2 with ⟨hne, _⟩ | ⟨_, hL⟩
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩))
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hL
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩))
    refine ⟨hr, ?_⟩
    refine ⟨hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2), ?_, ?_⟩
    · intro
      have hFstCon : fstFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.1)
      exact (treeSystem A).ent_bot hFstCon
    · intro
      have hsub : pairRFinset u ⊆
          sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro s hs
        exact (mem_sndFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(treeBot, s), ⟨Or.inl rfl⟩⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩),
            rfl, rfl⟩
      have hSndCon : sndFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.2)
      rcases h.2.2.2.2 with ⟨hne, hPay⟩ | ⟨rfl, _⟩
      · exact (treeSystem A).ent_trans hSndCon h.2.2.1
          (fun y hy => (treeSystem A).ent_refl hSndCon (hsub hy)) ⟨h.2.2.1, hPay⟩
      · exact (treeSystem A).ent_bot hSndCon

end DomainTheory.BridgeTheorems
