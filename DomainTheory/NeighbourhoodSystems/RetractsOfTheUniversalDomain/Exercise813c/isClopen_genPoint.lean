module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


theorem isClopen_genPoint (i : ℕ) : IsClopen (genPoint i) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply i)

end DomainTheory.NeighbourhoodSystems
