/-ai
The abstract atom of depth zero is the master neighbourhood of the system.

This is the zero clause of the recursive definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α γ : Type*}

variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomE_zero (δ : ℕ → Bool) : atomE E split X Δ δ 0 = E.master := rfl

end DomainTheory.NeighbourhoodSystems
