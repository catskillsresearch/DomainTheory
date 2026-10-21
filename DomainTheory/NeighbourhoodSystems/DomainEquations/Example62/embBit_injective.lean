/-ai
Tagging by one fixed boolean is injective on sets of binary strings.

Equality of the tagged sets yields inclusion in each direction, and one tagging by that boolean is contained in the other exactly when the underlying sets are so contained.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_subset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_injective {b : Bool} {X X' : Set Str} (h : embBit b X = embBit b X') : X = X' :=
  Set.Subset.antisymm (embBit_subset.mp h.subset) (embBit_subset.mp h.symm.subset)

end Example62

end DomainTheory.NeighbourhoodSystems
