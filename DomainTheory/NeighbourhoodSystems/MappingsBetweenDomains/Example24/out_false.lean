module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem out_false (t : Str) : out (false :: t) = false :: out t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
