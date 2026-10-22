module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.atomU_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.SplitSpec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

variable (X : ℕ → Set α) (Δ : Set α)

variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)

include hΔ hsplit

/-- Restrict `δ : ℕ → Bool` to `Fin n → Bool`. -/
def restrictFin (δ : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => δ i.val

end DomainTheory.NeighbourhoodSystems
