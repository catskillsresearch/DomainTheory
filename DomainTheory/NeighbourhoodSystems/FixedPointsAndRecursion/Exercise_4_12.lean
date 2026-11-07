module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.noGreatestFixed

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap TwoToken TwoToken.neighborhoodSystem

theorem example_412 :
    (∀ (x : noGreatestFixedDomain.Element),
      (idMap noGreatestFixedDomain).toElementMap x = x) ∧
    (¬ ∃ z : noGreatestFixedDomain.Element,
      (idMap noGreatestFixedDomain).toElementMap z = z ∧
        ∀ x, (idMap noGreatestFixedDomain).toElementMap x = x → x ≤ z) :=
  ⟨@idMap_fixed, @no_greatest_fixedPoint⟩

