module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prod_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_fst
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_snd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.pair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_pair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem mem_pair_prodNbhd {x : V₀.Element} {y : V₁.Element} {X : Set α} {Y : Set β} :
    (pair x y).mem (prodNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

end DomainTheory.NeighbourhoodSystems
