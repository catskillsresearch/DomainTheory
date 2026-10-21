/-ai
The abstract atom is the neighbourhood in the target system obtained by splitting, depth by depth, according to a Boolean sequence. At depth zero it is the master neighbourhood. At depth n + 1 it is the first or second component of the split of the generated atom, the atom already built, and the n-th set, according as the n-th bit is true or false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α γ : Type*}

variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)

/-- The `E`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` satisfying `SplitSpec' E split`. Generalizes `Theorem88.lean`'s `atomU` from the
hardcoded target `U` to an abstract `E`. -/
noncomputable def atomE (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set γ
  | 0 => E.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2

end DomainTheory.NeighbourhoodSystems
