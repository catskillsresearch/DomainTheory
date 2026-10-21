/-ai
The output of a leading zero followed by a tail is zero followed by the output of the tail.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **A leading `0` always emits it and continues copying.** `out([0]++τ) = 0::out τ`, for every
tail `τ`. (Exercise 2.17's first equation, at the token level.) -/
theorem out_append_false (τ : Str) : out ([false] ++ τ) = false :: out τ := rfl

end DomainTheory.NeighbourhoodSystems.Example24
