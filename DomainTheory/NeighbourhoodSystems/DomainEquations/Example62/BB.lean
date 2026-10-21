/-ai
The sum of the binary-sequence domain with itself is the neighbourhood system appearing on the right-hand side of the domain equation for that domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- The right-hand side of Scott's domain equation: the sum system `B + B` (Exercise 3.18). -/
abbrev BB : NeighborhoodSystem (Option (Str ⊕ Str)) := sum B B B_nonempty B_nonempty

end Example62

end DomainTheory.NeighbourhoodSystems
