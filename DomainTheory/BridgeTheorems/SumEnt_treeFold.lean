/-ai
If the unfolding of a finite set of tree tokens entails a sum token, then the set entails the tree fold of that sum token.

Consistency of the unfolding gives consistency of the tree set. A bottom sum token has a trivial entailment payload. A left atom has its atom-consistency and its atom-entailment transported across the identification of the left part of the unfolding with the atom set. For a right product token the left part is empty, because the right part is nonempty, so the atom set is empty. When the product's right component is tree bottom, the fold is pair-left of the left component. The first projection of the right part entails that component and is contained in the pair-left set with bottom inserted, since a first component is a pair-left token or the bottom coming from a pair-right token, and entailment transfers to the enlarged pair-left set. A token of the nonempty right part is a pair-left token or a pair-right token. In the first subcase entailment transfers back to the pair-left set, dropping bottom by entailment of bottom and keeping pair-left tokens by reflexivity. In the second subcase, a bottom left component is the other disjunct of the payload, while a non-bottom left component forces the pair-left set to be nonempty, because an empty pair-left set would make the enlarged set a singleton of bottom and force the component to be bottom, and entailment again transfers back. When the product's right component is not tree bottom, the product token has left component bottom and the fold is pair-right of the right component. The second projection entails that component and is contained in the pair-right set with bottom inserted, so entailment transfers to the enlarged set and then back to the pair-right set, which is nonempty because emptiness would force the right component to be bottom.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.TreeProd
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.lftFinset_image_unfold
public import DomainTheory.BridgeTheorems.rhtFinset_image_unfold_mem
public import DomainTheory.BridgeTheorems.SumCon_image_treeCon

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem SumEnt_treeFold {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))}
    (h : SumEnt A (TreeProd A) (unfoldFinset A u) s) :
    TreeEnt A u (treeFold A s) := by
  have hu : TreeCon A u := SumCon_image_treeCon A h.1
  refine ⟨hu, ?_⟩
  cases s with
  | bot => exact trivial
  | left x =>
    dsimp [treeFold]
    refine ⟨?_, ?_⟩
    · rw [← lftFinset_image_unfold A u]; exact h.2.1
    · rw [← lftFinset_image_unfold A u]; exact h.2.2
  | right p =>
    dsimp [treeFold]
    have hAt : atomFinset u = ∅ := by
      have hl := (lftFinset_image_unfold A u)
      have : lftFinset (unfoldFinset A u) = ∅ :=
        SumCon_lft_empty_of_rht_nonempty A (TreeProd A) h.1 h.2.1
      rwa [hl] at this
    split_ifs with hb
    · refine ⟨hAt, TreeCon_pairL_of_right A hu hAt, TreeCon_pairR_of_right A hu hAt, ?_⟩
      have hEnt := h.2.2
      -- ProdEnt: Ent fst p.1 (since p.2 = bot)
      have hFst : (treeSystem A).Ent
          (fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u))) p.val.1 :=
        hEnt.2.1 hb
      have hsub :
          fstFinset (treeSystem A) (treeSystem A)
              (rhtFinset (unfoldFinset A u)) ⊆
            insert .bot (pairLFinset u) := by
        intro t ht
        rcases (mem_fstFinset (treeSystem A) (treeSystem A)).1 ht with ⟨q, hq, _, rfl⟩
        rcases (rhtFinset_image_unfold_mem A u q).1 hq with ⟨w, hw, hq'⟩ | ⟨w, hw, hq'⟩
        · subst hq'; exact Finset.mem_insert_of_mem (mem_pairLFinset.2 hw)
        · subst hq'; exact Finset.mem_insert_self _ _
      -- Transfer Ent along the subset into pairL ∪ {bot}
      have hIns : TreeCon A (insert .bot (pairLFinset u)) :=
        TreeCon_insert_bot A (TreeCon_pairL_of_right A hu hAt)
      have hPay : TreeEntPayload A (insert .bot (pairLFinset u)) p.val.1 :=
        ((treeSystem A).ent_trans hIns
          (SumCon_rht_con_of_rht_nonempty A (TreeProd A) h.1 h.2.1).1
          (fun y hy => (treeSystem A).ent_refl hIns (hsub hy)) hFst).2
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty h.2.1
      rcases (rhtFinset_image_unfold_mem A u y).1 hy with ⟨w, hwL, _⟩ | ⟨w, hwR, _⟩
      · refine Or.inl ⟨Finset.ne_empty_of_mem (mem_pairLFinset.2 hwL), ?_⟩
        exact ((treeSystem A).ent_trans (TreeCon_pairL_of_right A hu hAt) hIns
          (fun z hz => by
            rw [Finset.mem_insert] at hz
            rcases hz with rfl | hz
            · exact (treeSystem A).ent_bot (TreeCon_pairL_of_right A hu hAt)
            · exact (treeSystem A).ent_refl (TreeCon_pairL_of_right A hu hAt) hz)
          ⟨hIns, hPay⟩).2
      · if ht : p.val.1 = .bot then
          exact Or.inr ⟨ht, Finset.ne_empty_of_mem (mem_pairRFinset.2 hwR)⟩
        else
          refine Or.inl ⟨?_, ?_⟩
          · intro hempty
            have hEq : insert (.bot : TreeToken α) (pairLFinset u) = {.bot} := by
              rw [hempty]; rfl
            exact ht (TreeEntPayload_of_no_atoms_no_pairs A
              atomFinset_singleton_bot pairLFinset_singleton_bot
              pairRFinset_singleton_bot (hEq ▸ hPay))
          · exact ((treeSystem A).ent_trans (TreeCon_pairL_of_right A hu hAt) hIns
              (fun z hz => by
                rw [Finset.mem_insert] at hz
                rcases hz with rfl | hz
                · exact (treeSystem A).ent_bot (TreeCon_pairL_of_right A hu hAt)
                · exact (treeSystem A).ent_refl (TreeCon_pairL_of_right A hu hAt) hz)
              ⟨hIns, hPay⟩).2
    · -- pairR p.2
      refine ⟨hAt, TreeCon_pairR_of_right A hu hAt, TreeCon_pairL_of_right A hu hAt, ?_⟩
      have ha : p.val.1 = treeBot := by
        rcases p.property with h1 | h2
        · exact h1
        · exact False.elim (hb h2)
      have hEnt := h.2.2
      have hSnd : (treeSystem A).Ent
          (sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u))) p.val.2 :=
        hEnt.2.2 ha
      have hIns : TreeCon A (insert .bot (pairRFinset u)) :=
        TreeCon_insert_bot A (TreeCon_pairR_of_right A hu hAt)
      have hsub :
          sndFinset (treeSystem A) (treeSystem A)
              (rhtFinset (unfoldFinset A u)) ⊆
            insert .bot (pairRFinset u) := by
        intro t ht
        rcases (mem_sndFinset (treeSystem A) (treeSystem A)).1 ht with ⟨q, hq, _, rfl⟩
        rcases (rhtFinset_image_unfold_mem A u q).1 hq with ⟨w, hw, hq'⟩ | ⟨w, hw, hq'⟩
        · subst hq'; exact Finset.mem_insert_self _ _
        · subst hq'; exact Finset.mem_insert_of_mem (mem_pairRFinset.2 hw)
      have hPay : TreeEntPayload A (insert .bot (pairRFinset u)) p.val.2 :=
        ((treeSystem A).ent_trans hIns
          (SumCon_rht_con_of_rht_nonempty A (TreeProd A) h.1 h.2.1).2
          (fun y hy => (treeSystem A).ent_refl hIns (hsub hy)) hSnd).2
      refine Or.inl ⟨?_, ?_⟩
      · intro hempty
        have hEq : insert (.bot : TreeToken α) (pairRFinset u) = {.bot} := by
          rw [hempty]; rfl
        have ht : p.val.2 = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (hEq ▸ hPay)
        exact hb (ht ▸ rfl)
      · exact ((treeSystem A).ent_trans (TreeCon_pairR_of_right A hu hAt) hIns
          (fun z hz => by
            rw [Finset.mem_insert] at hz
            rcases hz with rfl | hz
            · exact (treeSystem A).ent_bot (TreeCon_pairR_of_right A hu hAt)
            · exact (treeSystem A).ent_refl (TreeCon_pairR_of_right A hu hAt) hz)
          ⟨hIns, hPay⟩).2

end DomainTheory.BridgeTheorems
