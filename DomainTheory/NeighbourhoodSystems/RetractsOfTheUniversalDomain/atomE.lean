module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

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
