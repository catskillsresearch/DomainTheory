module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.basicOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_basicOpen {X : Set α} {x : V.Element} :
    x ∈ V.basicOpen X ↔ x.mem X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
