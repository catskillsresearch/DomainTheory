module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The filter of `{[X]}` *fixed by* the point `x ∈ |𝒟|` is `toToken x` (the filter of all
brackets containing `x`). By Theorem 1.10 this is a bijection `|𝒟| ≃ |{[X]}|`, so tokens and
(partial) elements are identified. -/
def filterFixedBy (x : V.Element) : V.tokenSystem.Element := V.toToken x

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
