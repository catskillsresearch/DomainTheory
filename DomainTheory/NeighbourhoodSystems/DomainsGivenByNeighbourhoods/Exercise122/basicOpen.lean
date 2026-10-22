/-ai
The basic open of a set is the set of elements that contain the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Theorem 1.10 notation): the set of elements of the domain
`|𝒟|` that contain the neighbourhood `X`. These sets are the basic opens of the topology of
Exercise 1.22. -/
def basicOpen (X : Set α) : Set V.Element := {x | x.mem X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
