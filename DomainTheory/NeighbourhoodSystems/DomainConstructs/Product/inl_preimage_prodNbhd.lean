/-ai
The left preimage of the product neighbourhood of X and Y is X.

The two sets have the same members by the membership lemmas for product neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem inl_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inl ⁻¹' prodNbhd X Y = X := by ext a; simp

end DomainTheory.NeighbourhoodSystems
