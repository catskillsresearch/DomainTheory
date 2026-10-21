/-ai
This file gathers and re-exports approximable maps, their elementwise action, identity and composition, the map induced by a domain isomorphism, and directed unions of elements, together with the order laws for directed unions, recovery of the relation from principal elements, monotonicity and extensionality of the elementwise action, the identity and associativity laws, the elementwise action of composition and of an isomorphism, existence of an approximable map inducing a given isomorphism, and preservation of principal elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.le_sSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.sSupDirected_le
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.rel_iff_mem_principal
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ext_of_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_comp
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_assoc
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_comp
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.exists_approximable_of_iso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.exists_principal_eq_apply_principal

@[expose] public section
