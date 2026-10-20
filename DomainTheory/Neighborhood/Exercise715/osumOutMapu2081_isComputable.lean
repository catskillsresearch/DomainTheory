/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Exercise715.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510



section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)



variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}









variable {h₀ h₁}







variable (P₀ P₁)


/-- **`out₁` is computable.** Symmetric to `out₀` via `rightPart`. -/
theorem osumOutMap₁_isComputable :
    IsComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) P₁.toScott osumOutMap₁ := by
  obtain ⟨k1, hk1⟩ := P₁.surj V₁.master_mem
  have hT1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have hIncR : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ⊆ P₁.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₁.incl_computable.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hIncM : RecDecidable (fun t => V₁.master ⊆ P₁.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd, hk1])
      (P₁.incl_computable.comp ((Nat.Primrec.const k1).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT1.and (hP1.and hIncR)).or ((hT1.and hP1).not.and hIncM))).re
  show (osumOutMap₁ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2) ↔ _
  rw [show (osumOutMap₁ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2)
      ↔ rightPart V₁ (osumEnum P₀ P₁ t.unpair.1) ⊆ P₁.X t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨osumEnum_mem h₀ h₁ _, P₁.mem_X _, h⟩⟩]
  by_cases hR : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
  · rw [osumEnum_right hR, rightPart_inj₁]
    exact ⟨fun h => Or.inl ⟨hR.1, hR.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hR h.1)⟩
  · by_cases hL : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
    · rw [osumEnum_left hL, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _))]
      exact ⟨fun h => Or.inr ⟨hR, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hR) (fun h => h.2)⟩
    · rw [osumEnum_master hL hR, rightPart_sumMaster]
      exact ⟨fun h => Or.inr ⟨hR, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hR) (fun h => h.2)⟩

end Coalesced
end DomainTheory.Neighborhood
