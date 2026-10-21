/-ai
The right preimage of the product neighbourhood of X and Y is Y.

The two sets have the same members by the membership lemmas for product neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem inr_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inr ⁻¹' prodNbhd X Y = Y := by ext b; simp

end DomainTheory.NeighbourhoodSystems
