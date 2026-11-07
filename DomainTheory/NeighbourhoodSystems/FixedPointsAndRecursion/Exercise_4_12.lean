module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.noGreatestFixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem

theorem example_412 :
    (∀ (x : noGreatestFixedDomain.Element),
      (idMap noGreatestFixedDomain).toElementMap x = x) ∧
    (¬ ∃ z : noGreatestFixedDomain.Element,
      (idMap noGreatestFixedDomain).toElementMap z = z ∧
        ∀ x, (idMap noGreatestFixedDomain).toElementMap x = x → x ≤ z) :=
  ⟨@idMap_fixed, @no_greatest_fixedPoint⟩

end DomainTheory.NeighbourhoodSystems
