module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel

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

section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **The smash of two maps `f ⊗ g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀' ⊗ 𝒟₁'`.** -/
def smashMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (smash V₀ V₁) (smash V₀' V₁') where
  rel W W' := (smash V₀ V₁).mem W ∧ (smash V₀' V₁').mem W' ∧
    (W' = prodNbhd V₀'.master V₁'.master ∨
      ∃ A B A' B', W = prodNbhd A B ∧ W' = prodNbhd A' B' ∧
        A' ≠ V₀'.master ∧ B' ≠ V₁'.master ∧ f.rel A A' ∧ g.rel B B')
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, (smash V₀' V₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have key : W'₁ ∩ W'₂ = prodNbhd V₀'.master V₁'.master ∨
        ∃ A B A' B', W = prodNbhd A B ∧ W'₁ ∩ W'₂ = prodNbhd A' B' ∧
          A' ≠ V₀'.master ∧ B' ≠ V₁'.master ∧ f.rel A A' ∧ g.rel B B' := by
      rcases hd₁ with rfl | ⟨A, B, A'₁, B'₁, hWAB, rfl, hA'₁, hB'₁, hf₁, hg₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ prodNbhd V₀'.master V₁'.master from
          (smash V₀' V₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨A₂, B₂, A'₂, B'₂, hWAB₂, rfl, hA'₂, hB'₂, hf₂, hg₂⟩
        · rw [Set.inter_eq_left.mpr (show prodNbhd A'₁ B'₁ ⊆ prodNbhd V₀'.master V₁'.master from
            (smash V₀' V₁').sub_master hW'₁)]
          exact Or.inr ⟨A, B, A'₁, B'₁, hWAB, rfl, hA'₁, hB'₁, hf₁, hg₁⟩
        · obtain ⟨rfl, rfl⟩ := prodNbhd_injective (hWAB.symm.trans hWAB₂)
          rw [prodNbhd_inter]
          exact Or.inr ⟨A, B, A'₁ ∩ A'₂, B'₁ ∩ B'₂, hWAB, rfl,
            inter_ne_master_left (f.rel_cod hf₁) hA'₁,
            inter_ne_master_left (g.rel_cod hg₁) hB'₁,
            f.inter_right hf₁ hf₂, g.inter_right hg₁ hg₂⟩
    refine ⟨hW, ?_, key⟩
    rcases key with hm | ⟨A, B, A', B', -, hWW', hA', hB', hf, hg⟩
    · rw [hm]; exact (smash V₀' V₁').master_mem
    · rw [hWW']; exact smash_mem_proper (f.rel_cod hf) hA' (g.rel_cod hg) hB'
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨A, B, A', B', rfl, rfl, hA', hB', hf, hg⟩
    · left; exact Set.Subset.antisymm ((smash V₀' V₁').sub_master hW'₂mem) hW'W'₂
    · obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := smash_mem_prodNbhd_form hW₂mem
      obtain ⟨hA₂A, hB₂B⟩ := prodNbhd_subset_iff.mp hW₂W
      rcases smash_mem_iff.mp hW'₂mem with rfl |
        ⟨A'₂, B'₂, hA'₂, hA'₂ne, hB'₂, hB'₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hA'A'₂, hB'B'₂⟩ := prodNbhd_subset_iff.mp hW'W'₂
        exact Or.inr ⟨A₂, B₂, A'₂, B'₂, rfl, rfl, hA'₂ne, hB'₂ne,
          f.mono hf hA₂A hA'A'₂ hA₂ hA'₂, g.mono hg hB₂B hB'B'₂ hB₂ hB'₂⟩

end SmashFunctor

end Smash

end DomainTheory.NeighbourhoodSystems
