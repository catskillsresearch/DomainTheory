/-ai
A point lies in a coordinate set if and only if its value at that coordinate is true.

The two sides are definitionally the same.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.genPoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

@[simp] theorem mem_genPoint {i : ℕ} {x : ℕ → Bool} : x ∈ genPoint i ↔ x i = true := Iff.rfl

end DomainTheory.NeighbourhoodSystems
