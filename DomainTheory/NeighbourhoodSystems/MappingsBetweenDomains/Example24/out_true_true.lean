module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Cons-form restatement of `out_append_trueTrue`, for peeling one token at a time in `key`. -/
theorem out_true_true (t : Str) : out (true :: true :: t) = out (true :: t) := rfl

end DomainTheory.NeighbourhoodSystems.Example24
