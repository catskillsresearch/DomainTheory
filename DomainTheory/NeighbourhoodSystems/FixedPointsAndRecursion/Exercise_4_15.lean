module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.maximalFixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

theorem example_415 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∃ b, f b = b ∧ ∀ y, f y = y → b ≤ y) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∃ m, f m = m ∧ ∀ y, f y = y → m ≤ y → y ≤ m) :=
  ⟨@exists_least_fixedPoint, @exists_maximal_fixedPoint⟩

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
