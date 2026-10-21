/-ai
Theorem 3.5 of Scott (1981, PRG-19), in the direction from separate to joint approximability, sends a two-variable approximable map to the joint map that relates a product neighbourhood W to Z when W is a product neighbourhood and the two-variable map relates the left and right preimages of W to Z. The master relation and right intersection are inherited. Monotonicity decomposes the smaller product neighbourhood into its components and applies monotonicity of the two-variable map to the preimages.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.constMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_constMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Theorem 3.5 (←) (Scott 1981, PRG-19).** A two-variable mapping induces a joint mapping. -/
def ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ f.rel (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) Z
  rel_dom h := h.1
  rel_cod h := f.rel_cod h.2
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    simpa using f.master_rel
  inter_right := by rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩; exact ⟨hW, f.inter_right hrel hrel'⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl
    rw [inr_preimage_prodNbhd] at hinr
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact f.mono hrel hinl hinr hZZ' hA hB hZ'

end DomainTheory.NeighbourhoodSystems
