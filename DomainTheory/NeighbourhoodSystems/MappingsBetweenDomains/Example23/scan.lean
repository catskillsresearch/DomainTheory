module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The parity scanner.** `scan σ = none` while `σ` is an unbroken run of `0`'s; once a `1`
appears, `scan σ = some b` with `b = true` iff an even number of `0`'s preceded it. A leading `0`
flips the parity of the rest; a leading `1` fixes parity `true` (zero preceding zeros). -/
def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)

end DomainTheory.NeighbourhoodSystems.Example23
