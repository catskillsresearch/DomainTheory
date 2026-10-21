/-ai
The deletion scan of a string beginning with zero is the string itself.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_true

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem del_false (t : Str) : del (false :: t) = false :: t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
