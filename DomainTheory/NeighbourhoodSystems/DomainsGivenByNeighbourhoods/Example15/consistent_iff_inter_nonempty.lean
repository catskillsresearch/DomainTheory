module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
import all Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem










/-- **Factoid 1.5a (Scott 1981, PRG-19).** In Example 1.5, "sets are consistent in `𝒟` iff they
have a non-empty intersection": a finite prefix `X₀, …, Xₙ₋₁` is consistent exactly when its
intersection `⋂_{i<n} Xᵢ` is non-empty. -/
theorem consistent_iff_inter_nonempty (X : ℕ → Set Token) (n : ℕ) :
    neighborhoodSystem.Consistent X n ↔ (neighborhoodSystem.interUpTo X n).Nonempty := by
  constructor
  · rintro ⟨Z, hZ, hsub⟩
    obtain ⟨z, hz⟩ := hZ
    exact ⟨z, hsub hz⟩
  · intro h
    exact ⟨_, h, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Example15
