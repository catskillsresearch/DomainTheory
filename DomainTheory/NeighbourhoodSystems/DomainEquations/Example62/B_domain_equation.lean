/-ai
The binary-sequence domain is isomorphic, as a domain, to the sum of that domain with itself.

The witnessing isomorphism of elements is the order equivalence between the domain and the sum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62


/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `B ≅ B + B`.** Scott's binary-sequence
domain `B` is, as a domain, isomorphic to `B + B`: a sequence is bottom, or begins with `0`, or begins
with `1`, the two non-bottom cases giving the two summands. -/
theorem B_domain_equation : B ≅ᴰ sum B B B_nonempty B_nonempty :=
  ⟨bbEquiv⟩

end Example62
end DomainTheory.NeighbourhoodSystems
