/-ai
Scott's sequence at stage n, relative to a splitting operation and an enumeration with nonempty master set, is the union, over all sign sequences of length n, of the U-side atom of depth n + 1 of the sequence padded by true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.atomU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.atomU_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.extendTrue
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.SplitSpec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

variable (X : ℕ → Set α) (Δ : Set α)

variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)

include hΔ hsplit

/-- **Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the "+"-piece chosen when
splitting against `X n`. -/
noncomputable def Yseq (n : ℕ) : Set ℚ :=
  ⋃ δ' : Fin n → Bool, atomU split X Δ (extendTrue δ') (n + 1)

end DomainTheory.NeighbourhoodSystems
