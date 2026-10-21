/-ai
The domain of the powerset system is order-isomorphic to the powerset of the natural numbers. The forward map reads the set represented by an element and the inverse builds the filter of a set, and the two round trips are the mutual inverse lemmas. If the represented sets are ordered, monotonicity of the filter construction and cancellation of those round trips recover the inequality of elements; an inequality of elements passes to membership of each singleton complement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
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
