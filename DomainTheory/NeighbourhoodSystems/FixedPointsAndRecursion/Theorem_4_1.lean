module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixElement

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Theorem 4.1: every endomap has a least fixed point. -/
theorem theorem_41 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V),
      f.toElementMap f.fixElement = f.fixElement) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) {z : V.Element},
      f.toElementMap z ≤ z → f.fixElement ≤ z) :=
  ⟨@toElementMap_fixElement, @fixElement_le_of_toElementMap_le⟩

end DomainTheory.NeighbourhoodSystems
