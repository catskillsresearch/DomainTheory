/-ai
The bracket of a set of tokens is the set of elements that contain the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}`: the elements of `|𝒟|` that contain the neighbourhood `X`.
(This is the `basicOpen X` of Exercise 1.22, repeated here to avoid the topology dependency.) -/
def bracket (X : Set α) : Set V.Element := {x | x.mem X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
