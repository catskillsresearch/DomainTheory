/-ai
Definition 3.3 of Scott (1981, PRG-19) pairs approximable maps f and g as the map that relates an input Z to a product neighbourhood P when P is a product neighbourhood, f relates Z to the left preimage of P, and g relates Z to the right preimage. The master relation is the pair of master relations. Right intersection uses the intersection laws of f and g and rebuilds the product of the intersected preimages. Monotonicity decomposes the larger product neighbourhood and applies monotonicity of f and of g on the two preimages.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.fst_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.snd_pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_preimage

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- **Definition 3.3 (Scott 1981, PRG-19).** The paired mapping `⟨f, g⟩ : 𝒟₂ → 𝒟₀ × 𝒟₁`,
`Z ⟨f, g⟩ (X ∪ Y) ↔ Z f X ∧ Z g Y`. -/
def paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    ApproximableMap V₂ (prod V₀ V₁) where
  rel Z P := (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P)
  rel_dom h := f.rel_dom h.2.1
  rel_cod h := h.1
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_, ?_⟩
    · simpa using f.master_rel
    · simpa using g.master_rel
  inter_right := by
    rintro Z P P' ⟨hP, hfP, hgP⟩ ⟨hP', hfP', hgP'⟩
    have hfX := f.inter_right hfP hfP'
    have hgY := g.inter_right hgP hgP'
    refine ⟨?_, ?_, ?_⟩
    · rw [prodNbhd_preimage hP, prodNbhd_preimage hP', prodNbhd_inter]
      exact prod_mem_prodNbhd (f.rel_cod hfX) (g.rel_cod hgY)
    · rw [Set.preimage_inter]; exact hfX
    · rw [Set.preimage_inter]; exact hgY
  mono := by
    rintro Z Z₂ P P₂ ⟨_, hfP, hgP⟩ hZ₂Z hPP₂ hZ₂ hP₂
    obtain ⟨A, B, hA, hB, rfl⟩ := hP₂
    have hinl : Sum.inl ⁻¹' P ⊆ A := by
      have := Set.preimage_mono (f := Sum.inl) hPP₂; rwa [inl_preimage_prodNbhd] at this
    have hinr : Sum.inr ⁻¹' P ⊆ B := by
      have := Set.preimage_mono (f := Sum.inr) hPP₂; rwa [inr_preimage_prodNbhd] at this
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]; exact f.mono hfP hZ₂Z hinl hZ₂ hA
    · rw [inr_preimage_prodNbhd]; exact g.mono hgP hZ₂Z hinr hZ₂ hB

end DomainTheory.NeighbourhoodSystems
