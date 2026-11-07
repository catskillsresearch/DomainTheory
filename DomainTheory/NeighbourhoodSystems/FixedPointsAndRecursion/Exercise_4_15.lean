module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.maximalFixed

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Exercise 4.15: least and maximal fixed points of monotone maps. -/
theorem example_415 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∃ b, f b = b ∧ ∀ y, f y = y → b ≤ y) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∃ m, f m = m ∧ ∀ y, f y = y → m ≤ y → y ≤ m) :=
  ⟨@exists_least_fixedPoint, @exists_maximal_fixedPoint⟩
