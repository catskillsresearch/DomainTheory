/-ai
The true padding of a sign sequence of length n reads the sequence at every index below n and reads true at every later index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi
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

/-- Pad `δ' : Fin n → Bool` to a total `ℕ → Bool`, filling positions `≥ n` with `true`. -/
def extendTrue {n : ℕ} (δ' : Fin n → Bool) : ℕ → Bool :=
  fun i => if h : i < n then δ' ⟨i, h⟩ else true

end DomainTheory.NeighbourhoodSystems
