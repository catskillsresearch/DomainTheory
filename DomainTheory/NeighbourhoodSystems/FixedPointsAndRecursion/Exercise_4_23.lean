module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.uniqueFixed

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

open ApproximableMap

theorem example_423 :
    ∀ {α : Type*} {V : NeighborhoodSystem α}
      (f : ApproximableMap V V) (a : ℕ → ApproximableMap V V),
      (∀ x, (a 0).toElementMap x = V.bot) →
      (∀ x, IsLUB {y | ∃ n, y = (a n).toElementMap x} x) →
      (∀ n x, (a (n + 1)).toElementMap (f.toElementMap x) =
        (a (n + 1)).toElementMap (f.toElementMap ((a n).toElementMap x))) →
      ∃! x, f.toElementMap x = x :=
  @f_unique_fixedPoint

