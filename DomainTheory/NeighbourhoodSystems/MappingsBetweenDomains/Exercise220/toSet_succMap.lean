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
