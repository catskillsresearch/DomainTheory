module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet_ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — the identification `|𝒫| ≅ (Set ℕ, ⊆)`.** -/
def equivSetNat : powerSet.Element ≃o Set ℕ where
  toFun := toSet
  invFun := ofSet
  left_inv := ofSet_toSet
  right_inv := toSet_ofSet
  map_rel_iff' := by
    intro x y
    show toSet x ≤ toSet y ↔ x ≤ y
    constructor
    · intro h
      have hmono := ofSet_mono h
      rwa [ofSet_toSet, ofSet_toSet] at hmono
    · intro h n hn
      exact h _ hn

end DomainTheory.NeighbourhoodSystems.Exercise220
