module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.equivSetNat
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.succSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.succMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.unionMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.interMap₂
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_inter_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_compl_of_finite
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet_ofSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_predSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.succSet_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.predSet_mono

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
