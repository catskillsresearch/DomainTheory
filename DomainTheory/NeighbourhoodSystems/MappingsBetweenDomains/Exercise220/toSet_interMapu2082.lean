/-ai
The set represented by the intersection of two elements is the intersection of the sets they represent.

A number whose singleton complement belongs to the intersection comes from input neighbourhoods whose union is contained in that singleton complement, so the number lies in neither input neighbourhood and each element contains the singleton complement. Conversely, the two copies of the singleton complement are neighbourhoods of the two elements, and their union is contained in the singleton complement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem toSet_interMap₂ (x y : powerSet.Element) :
    toSet (interMap₂.toElementMap₂ x y) = toSet x ∩ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_inter_iff]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    have hkX : k ∉ X := fun h => (hsub (Or.inl h)) rfl
    have hkY : k ∉ Y := fun h => (hsub (Or.inr h)) rfl
    exact ⟨x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX),
      y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)⟩
  · rintro ⟨hkx, hky⟩
    exact ⟨{k}ᶜ, {k}ᶜ, hkx, hky, mem_compl_singleton k, mem_compl_singleton k,
      mem_compl_singleton k, Set.union_subset subset_rfl subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
