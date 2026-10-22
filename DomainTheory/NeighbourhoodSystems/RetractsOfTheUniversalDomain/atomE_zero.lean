module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α γ : Type*}

variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomE_zero (δ : ℕ → Bool) : atomE E split X Δ δ 0 = E.master := rfl

end DomainTheory.NeighbourhoodSystems
