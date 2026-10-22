module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_bracket {X : Set α} {x : V.Element} : x ∈ V.bracket X ↔ x.mem X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
