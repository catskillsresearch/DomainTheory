module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.isClopen_genPoint

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


theorem isOpen_genPoint (i : ℕ) : IsOpen (genPoint i) := (isClopen_genPoint i).isOpen

end DomainTheory.NeighbourhoodSystems
