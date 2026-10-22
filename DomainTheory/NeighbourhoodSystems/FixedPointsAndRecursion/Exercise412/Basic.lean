module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem

/-- Abbreviation for Example 1.2's domain `T`. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- `{1} ≠ {0}` as tokens. -/
theorem one_ne_zero : (Example12.one) ≠ Example12.zero := by
  intro h
  rw [Example12.one, Example12.zero, Set.ext_iff] at h
  have h1 : (1 : Example12.Token) = 0 := (h 1).mp rfl
  exact absurd h1 (by decide)

/-- `{1} ≠ Δ` as tokens. -/
theorem one_ne_master : (Example12.one) ≠ Example12.master := by
  intro h
  rw [Example12.one, Example12.master, Set.ext_iff] at h
  have h0 : (0 : Example12.Token) ∈ ({1} : Set Example12.Token) := (h 0).mpr (Set.mem_univ 0)
  simp only [Set.mem_singleton_iff] at h0
  exact absurd h0 (by decide)

/-- `{0} ≠ Δ` as tokens. -/
theorem zero_ne_master : (Example12.zero) ≠ Example12.master := by
  intro h
  rw [Example12.zero, Example12.master, Set.ext_iff] at h
  have h1 : (1 : Example12.Token) ∈ ({0} : Set Example12.Token) := (h 1).mpr (Set.mem_univ 1)
  simp only [Set.mem_singleton_iff] at h1
  exact absurd h1 (by decide)
end DomainTheory.NeighbourhoodSystems.Exercise412
