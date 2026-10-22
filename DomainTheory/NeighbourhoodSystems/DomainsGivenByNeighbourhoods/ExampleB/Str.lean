module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The token type `Σ* = List Bool` (finite binary strings); `Λ = []`. -/
abbrev Str := List Bool

end DomainTheory.NeighbourhoodSystems.ExampleB
