module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_mem_singleton
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_classify

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem








/-- **Flat: every atom is maximal (total).** -/
theorem flat_atom_maximal (n : ℕ) (y : flat.Element)
    (hle : flat.principal (flat_mem_singleton n) ≤ y) :
    y = flat.principal (flat_mem_singleton n) := by
  rcases flat_classify y with rfl | ⟨m, rfl⟩
  · exfalso
    have hmem : flat.bot.mem {n} := hle {n} ⟨flat_mem_singleton n, subset_rfl⟩
    rw [flat.mem_bot, flat_master] at hmem
    have : (n + 1) ∈ ({n} : Set ℕ) := by rw [hmem]; exact Set.mem_univ _
    simp at this
  · have hsub : ({m} : Set ℕ) ⊆ {n} :=
      (flat.principal_le_iff (flat_mem_singleton n) (flat_mem_singleton m)).mp hle
    obtain rfl : m = n := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
    rfl

end DomainTheory.NeighbourhoodSystems.Exercise115
