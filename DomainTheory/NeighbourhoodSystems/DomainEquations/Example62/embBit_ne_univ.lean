/-ai
The tagging of a set of binary strings by a boolean is distinct from the set of all binary strings.

If the tagging were the full set, the empty string would belong to the tagging, and the empty string belongs to no such tagging.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.nil_not_mem_embBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_ne_univ (b : Bool) (X : Set Str) : embBit b X ≠ Set.univ := by
  intro h; exact nil_not_mem_embBit (X := X) (b := b) (by rw [h]; trivial)

end Example62

end DomainTheory.NeighbourhoodSystems
