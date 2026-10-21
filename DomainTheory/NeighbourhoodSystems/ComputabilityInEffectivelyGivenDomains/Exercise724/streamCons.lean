/-ai
Prepending a natural number to an infinite stream sends zero to that number and sends each successor to the value of the original stream at the predecessor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- Prepend `i` to an infinite stream (`Stream'.cons`, spelled out by hand). -/
def streamCons (i : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => i
  | n + 1 => s n

end DomainTheory.NeighbourhoodSystems.Exercise724
