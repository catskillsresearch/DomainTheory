/-ai
The product of a neighbourhood of the first system and a neighbourhood of the second is a neighbourhood of the product system.

Those two neighbourhoods witness the existential membership of their product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem prod_mem_prodNbhd {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (prod V₀ V₁).mem (prodNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

end DomainTheory.NeighbourhoodSystems
