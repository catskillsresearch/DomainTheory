/-ai
The product of X and Y is a neighbourhood of the product system if and only if X and Y are neighbourhoods of the two systems.

If the product equals the product of some neighbourhoods, injectivity identifies the components. Conversely, a pair of neighbourhoods forms a product neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_injective
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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₀_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.proj₁_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.paired_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_proj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

theorem prod_mem_prodNbhd_iff {X : Set α} {Y : Set β} :
    (prod V₀ V₁).mem (prodNbhd X Y) ↔ V₀.mem X ∧ V₁.mem Y := by
  constructor
  · rintro ⟨A, B, hA, hB, heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hB⟩
  · rintro ⟨hX, hY⟩; exact prod_mem_prodNbhd hX hY

end DomainTheory.NeighbourhoodSystems
