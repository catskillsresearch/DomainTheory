/-ai
Each coordinate set is open in Cantor space.

It is clopen, and a clopen set is open.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.isClopen_genPoint

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems





theorem isOpen_genPoint (i : ℕ) : IsOpen (genPoint i) := (isClopen_genPoint i).isOpen

end DomainTheory.NeighbourhoodSystems
