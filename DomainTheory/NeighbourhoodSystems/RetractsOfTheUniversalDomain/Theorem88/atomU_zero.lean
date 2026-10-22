module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.atomU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomU_zero (δ : ℕ → Bool) : atomU split X Δ δ 0 = U.master := rfl

end DomainTheory.NeighbourhoodSystems
