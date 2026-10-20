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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_mem_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_mem_subset_inj₁

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

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

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)

/-- **The coalesced sum of two maps `f ⊕ g : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀' ⊕ 𝒟₁'`.** -/
def osumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (osum h₀ h₁) (osum h₀' h₁') where
  rel W W' := (osum h₀ h₁).mem W ∧ (osum h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, (osum h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y')) →
          (osum h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hY'ne, hf⟩ | ⟨_, Y', _, rfl, hY'ne, hg⟩)
      · exact (osum h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, hY'ne, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, hY'ne, rfl⟩)
    have key : W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y') := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hY'₁ne, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hY'₁ne, hg₁⟩
      · have he : sumMaster V₀' V₁' ∩ W'₂ = W'₂ :=
          Set.inter_eq_self_of_subset_right
            ((osum h₀' h₁').sub_master hW'₂ : W'₂ ⊆ sumMaster V₀' V₁')
        rw [he]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hY'₂ne, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hY'₂ne, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hY'₁ne, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl,
            inter_ne_master_left (f.rel_cod hf₁) hY'₁ne, f.inter_right hf₁ hf₂⟩)
        · exact absurd (hWX₁.symm.trans hWY₂)
            (fun h => not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hY'₂ne, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hY'₂ne, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hY'₁ne, hg₁⟩)
        · exact absurd (hWY₁.symm.trans hWX₂)
            (fun h => not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl,
            inter_ne_master_left (g.rel_cod hg₁) hY'₁ne, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hY'ne, hf⟩ | ⟨Y, Y', rfl, rfl, hY'ne, hg⟩
    · left; exact Set.Subset.antisymm ((osum h₀' h₁').sub_master hW'₂mem) hW'W'₂
    · obtain ⟨X₂, hX₂, hX₂ne, rfl⟩ := osum_mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, hY'₂ne, rfl⟩ | ⟨Z'₂, hZ'₂, hZ'₂ne, rfl⟩
      · left; rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl, hY'₂ne,
          f.mono hf hXX₂ (inj₀_subset_inj₀.mp hW'W'₂) hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    · obtain ⟨Y₂, hY₂, hY₂ne, rfl⟩ := osum_mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, hX'₂ne, rfl⟩ | ⟨Y'₂, hY'₂, hY'₂ne, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl, hY'₂ne,
          g.mono hg hYY₂ (inj₁_subset_inj₁.mp hW'W'₂) hY₂ hY'₂⟩)

end CoalescedFunctor

end Coalesced

end DomainTheory.NeighbourhoodSystems
