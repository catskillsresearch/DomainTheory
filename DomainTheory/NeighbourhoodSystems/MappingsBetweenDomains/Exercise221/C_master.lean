module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem C_master : C.master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems.Exercise221
