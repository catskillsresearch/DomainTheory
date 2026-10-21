/-ai
A Boolean function belongs to every box that pins coordinates to its own values.

At each pinned coordinate the required equality holds definitionally.
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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems








theorem self_mem_box (I : Finset ℕ) (f : ℕ → Bool) : f ∈ box I f := fun _ _ => rfl

end DomainTheory.NeighbourhoodSystems
