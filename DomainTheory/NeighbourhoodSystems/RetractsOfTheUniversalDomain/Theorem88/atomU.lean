/-ai
The U-side atom of an enumeration, a master set, and a sign sequence is the master neighbourhood of U at depth zero. At a successor depth it is the first or second output of splitting the generated atom and the previous U-side atom against the next enumerated set, according as the sign is true or false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.genAtom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

/-- The `U`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` (instantiated with `splitChoice` for Theorem 8.8(a), `splitEff` for 8.8(b)). -/
noncomputable def atomU (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set ℚ
  | 0 => U.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2

end DomainTheory.NeighbourhoodSystems
