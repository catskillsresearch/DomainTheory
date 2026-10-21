/-ai
The filter of the set represented by an element is the element itself.

Two elements are equal when they contain the same neighbourhoods. If a cofinite neighbourhood has its complement contained in the represented set, every member of that complement has its singleton complement in the element, so the finite-complement lemma puts the neighbourhood itself in the element. Conversely, a neighbourhood of the element remains a neighbourhood, and each member of its complement has its singleton complement above that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_of_finite

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem ofSet_toSet (x : powerSet.Element) : ofSet (toSet x) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hZsub⟩
    have hmem := mem_compl_of_finite x hZ (fun n hn => hZsub hn)
    rwa [compl_compl] at hmem
  · intro hZ
    refine ⟨x.sub hZ, ?_⟩
    intro n hn
    rw [mem_toSet]
    exact x.up_mem hZ (mem_compl_singleton n) (Set.subset_compl_singleton_iff.mpr hn)

end DomainTheory.NeighbourhoodSystems.Exercise220
