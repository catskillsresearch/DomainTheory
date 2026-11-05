module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- An ideal element is *total* when it is maximal in the approximation order. -/
def IsTotal (x : V.Element) : Prop := ∀ y, x ≤ y → y ≤ x

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
