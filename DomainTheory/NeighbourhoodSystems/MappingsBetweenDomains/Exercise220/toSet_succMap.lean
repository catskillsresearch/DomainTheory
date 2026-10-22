/-ai
The set represented by the successor of an element is the successor of the set represented by the element.

If the singleton complement of a number belongs to the image, some neighbourhood of the element has that number in the successor of its complement, so the number is one more than a member of the complement and the corresponding singleton complement lies above the neighbourhood. Conversely, the complement of the singleton of that predecessor belongs to the element, and the successor of its complement contains the original number.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem toSet_succMap (x : powerSet.Element) :
    toSet (succMap.toElementMap x) = succSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    obtain ⟨m, hm, rfl⟩ := hsub (Set.mem_singleton k)
    exact ⟨m, x.up_mem hxX (mem_compl_singleton m) (Set.subset_compl_singleton_iff.mpr hm), rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨{m}ᶜ, hm, mem_compl_singleton m, mem_compl_singleton (m + 1), ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    exact ⟨m, by rw [compl_compl]; exact Set.mem_singleton m, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
