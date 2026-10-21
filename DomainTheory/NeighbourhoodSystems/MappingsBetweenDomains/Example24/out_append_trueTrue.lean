/-ai
The output of two leading ones followed by a tail equals the output of one leading one followed by that tail.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB








/-- **A second consecutive `1` changes nothing.** `out([1,1]++τ) = out([1]++τ)`: once inside the
run of `1`'s, an extra `1` is simply swallowed by `del`. (Exercise 2.17's second equation, at the
token level — the recursive step behind the uniqueness argument for `runMap`.) -/
theorem out_append_trueTrue (τ : Str) : out ([true, true] ++ τ) = out ([true] ++ τ) := rfl

end DomainTheory.NeighbourhoodSystems.Example24
