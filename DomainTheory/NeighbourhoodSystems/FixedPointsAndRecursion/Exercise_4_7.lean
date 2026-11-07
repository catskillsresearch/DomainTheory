module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixAbove

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section

open NeighborhoodSystem

theorem example_407 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      {a : V.Element} (ha : a ≤ f.toElementMap a),
      f.toElementMap (f.fixAbove ha) = f.fixAbove ha) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
      {a : V.Element} (ha : a ≤ f.toElementMap a) {z : V.Element},
      a ≤ z → f.toElementMap z ≤ z → f.fixAbove ha ≤ z) :=
  ⟨@fixAbove_isFixed, @fixAbove_least⟩
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
