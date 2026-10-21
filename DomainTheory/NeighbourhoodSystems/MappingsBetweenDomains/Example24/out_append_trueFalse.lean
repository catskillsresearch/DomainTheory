/-ai
The output of a one, then a zero, then a tail, is zero followed by that tail.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB








/-- **`10` terminates the run and emits the `0`, whatever follows.** `out([1,0]++τ) = 0::τ`, for
every tail `τ`. (Exercise 2.17's third equation, at the token level.) -/
theorem out_append_trueFalse (τ : Str) : out ([true, false] ++ τ) = false :: τ := rfl

end DomainTheory.NeighbourhoodSystems.Example24
