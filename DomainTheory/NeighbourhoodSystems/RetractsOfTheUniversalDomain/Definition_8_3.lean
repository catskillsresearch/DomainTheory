module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.projection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Definition 8.3: a projection is a retraction below the identity, and
it is finitary when its fixed-point set is isomorphic to a domain. -/
theorem definition_83 {α : Type*} {E : NeighborhoodSystem α} (a : ApproximableMap E E) :
    (IsProjection a ↔ Retraction a ∧ a ≤ idMap E) ∧
      (FinitaryProjection a ↔ IsProjection a ∧ IsFinitary a) :=
  ⟨Iff.rfl, ⟨fun h => h.out, fun h => ⟨h⟩⟩⟩

end DomainTheory.NeighbourhoodSystems
