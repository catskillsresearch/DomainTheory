module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem toSet_ofSet (S : Set ℕ) : toSet (ofSet S) = S := by
  ext n
  simp only [mem_toSet]
  constructor
  · rintro ⟨_, hsub⟩
    rw [compl_compl] at hsub
    exact hsub (Set.mem_singleton n)
  · intro hn
    exact ⟨mem_compl_singleton n, by rw [compl_compl]; exact Set.singleton_subset_iff.mpr hn⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
