module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixAbove

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 4.7: fixAbove is a fixed point and the least one above a. -/
theorem example_407 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      {a : V.Element} (ha : a ≤ f.toElementMap a),
      f.toElementMap (f.fixAbove ha) = f.fixAbove ha) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      {a : V.Element} (ha : a ≤ f.toElementMap a) {z : V.Element},
      a ≤ z → f.toElementMap z ≤ z → f.fixAbove ha ≤ z) :=
  ⟨@fixAbove_isFixed, @fixAbove_least⟩
