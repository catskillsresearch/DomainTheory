/-ai
Scanning a leading one followed by any tail returns some true.

This is the true clause of the scanner.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **A leading `1` always commits to `true`, whatever follows.** `scan([1]++τ) = true`, for
*every* tail `τ`. (Exercise 2.16's first equation, at the token level.) -/
theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ

end DomainTheory.NeighbourhoodSystems.Example23
