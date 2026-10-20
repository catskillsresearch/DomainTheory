/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- **The strict pairing `⟨a, b⟩⊗ : 𝒟₂ → 𝒟₀ ⊗ 𝒟₁`.** Like Theorem 7.4's `paired`, but the smash
collapse forces the image factors to be proper (else the result is the master/bottom of the smash). -/
def smashPaired {V₂ : NeighborhoodSystem γ} (a : ApproximableMap V₂ V₀)
    (b : ApproximableMap V₂ V₁) : ApproximableMap V₂ (smash V₀ V₁) where
  rel Z W := V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
    (W = prodNbhd V₀.master V₁.master ∨
      ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₂.master_mem, (smash V₀ V₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro Z W₁ W₂ ⟨hZ, hW₁, hd₁⟩ ⟨-, hW₂, hd₂⟩
    have key : W₁ ∩ W₂ = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W₁ ∩ W₂ = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧
          a.rel Z A ∧ b.rel Z B := by
      rcases hd₁ with rfl | ⟨A₁, B₁, rfl, hA₁, hB₁, ha₁, hb₁⟩
      · rw [Set.inter_eq_right.mpr (show W₂ ⊆ prodNbhd V₀.master V₁.master from
          (smash V₀ V₁).sub_master hW₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨A₂, B₂, rfl, hA₂, hB₂, ha₂, hb₂⟩
        · rw [Set.inter_eq_left.mpr (show prodNbhd A₁ B₁ ⊆ prodNbhd V₀.master V₁.master from
            (smash V₀ V₁).sub_master hW₁)]
          exact Or.inr ⟨A₁, B₁, rfl, hA₁, hB₁, ha₁, hb₁⟩
        · rw [prodNbhd_inter]
          exact Or.inr ⟨A₁ ∩ A₂, B₁ ∩ B₂, rfl,
            inter_ne_master_left (a.rel_cod ha₁) hA₁,
            inter_ne_master_left (b.rel_cod hb₁) hB₁,
            a.inter_right ha₁ ha₂, b.inter_right hb₁ hb₂⟩
    refine ⟨hZ, ?_, key⟩
    rcases key with hm | ⟨A, B, hWW, hA, hB, ha, hb⟩
    · rw [hm]; exact (smash V₀ V₁).master_mem
    · rw [hWW]; exact smash_mem_proper (a.rel_cod ha) hA (b.rel_cod hb) hB
  mono := by
    rintro Z Z₂ W W₂ ⟨_, _, hd⟩ hZ₂Z hWW₂ hZ₂mem hW₂mem
    refine ⟨hZ₂mem, hW₂mem, ?_⟩
    rcases hd with rfl | ⟨A, B, rfl, hA, hB, ha, hb⟩
    · left; exact Set.Subset.antisymm ((smash V₀ V₁).sub_master hW₂mem) hWW₂
    · rcases smash_mem_iff.mp hW₂mem with rfl | ⟨A₂, B₂, hA₂, hA₂ne, hB₂, hB₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hAA₂, hBB₂⟩ := prodNbhd_subset_iff.mp hWW₂
        exact Or.inr ⟨A₂, B₂, rfl, hA₂ne, hB₂ne,
          a.mono ha hZ₂Z hAA₂ hZ₂mem hA₂, b.mono hb hZ₂Z hBB₂ hZ₂mem hB₂⟩

end Smash

end DomainTheory.NeighbourhoodSystems
