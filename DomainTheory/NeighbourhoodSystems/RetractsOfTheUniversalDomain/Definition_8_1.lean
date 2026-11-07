module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.retraction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Definition 8.1: a retraction is an approximable endomap equal to its
own composite. -/
theorem definition_81 {α : Type*} {E : NeighborhoodSystem α} (a : ApproximableMap E E) :
    Retraction a ↔ a.comp a = a :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

end DomainTheory.NeighbourhoodSystems
