module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singletonElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Lambda
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.juxtapose
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_not_subset_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_singleton_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singleton_cone_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singleton_singleton_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.nestedOrDisjoint_C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.subset_singleton_eq
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_prepend
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_subset_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Every neighbourhood of `𝒞` is nonempty (there is no empty token). -/
theorem memC_nonempty {W : Set Str} (hW : C.mem W) : W.Nonempty := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨σ, mem_cone.mpr List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
