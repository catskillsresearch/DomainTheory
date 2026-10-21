/-ai
A set belongs to the dual of a family if and only if its complement belongs to the family.

The two sides are definitionally the same.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

@[simp] theorem mem_dualFilter {α : Type*} {x : Set (Set α)} {Y : Set α} :
    Y ∈ dualFilter x ↔ Yᶜ ∈ x := Iff.rfl

end DomainTheory.NeighbourhoodSystems
