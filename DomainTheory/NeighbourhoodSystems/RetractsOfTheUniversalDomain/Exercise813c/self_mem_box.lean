module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


theorem self_mem_box (I : Finset ℕ) (f : ℕ → Bool) : f ∈ box I f := fun _ _ => rfl

end DomainTheory.NeighbourhoodSystems
