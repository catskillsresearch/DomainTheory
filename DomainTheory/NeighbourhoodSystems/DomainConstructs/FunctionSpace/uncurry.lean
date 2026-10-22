module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** Uncurrying `h : 𝒟₀ → (𝒟₁ → 𝒟₂)` to `𝒟₀ × 𝒟₁ → 𝒟₂`:
`X ∪ Y (uncurry h) Z ↔ X h [Y, Z]`. -/
def uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z)
  rel_dom h' := h'.1
  rel_cod := by
    rintro W Z ⟨_, hrel⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    exact f.rel_cod hf
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    rw [show (prod V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
      inl_preimage_prodNbhd, inr_preimage_prodNbhd, step_master_eq]
    exact h.master_rel
  inter_right := by
    rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    obtain ⟨f', hf'⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel')).2
    refine ⟨hW, ?_⟩
    rw [← step_inter_right (f.rel_cod hf) (f'.rel_cod hf')]
    exact h.inter_right hrel hrel'
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl ⊢
    rw [inr_preimage_prodNbhd] at hinr ⊢
    refine ⟨prod_mem_prodNbhd hA hB, ?_⟩
    exact h.mono hrel hinl (step_subset hB hZ' hinr hZZ') hA (step_mem hB hZ')

end DomainTheory.NeighbourhoodSystems
