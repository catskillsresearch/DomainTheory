/-ai
The U-side atom of depth zero is the master neighbourhood of U.

This is the zero clause of the U-side atom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.atomU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomU_zero (δ : ℕ → Bool) : atomU split X Δ δ 0 = U.master := rfl

end DomainTheory.NeighbourhoodSystems
