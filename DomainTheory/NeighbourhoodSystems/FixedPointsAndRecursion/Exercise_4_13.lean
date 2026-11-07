module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.monoFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

theorem example_413 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∀ {a : V.Element} (ha : f a ≤ a),
        f (monoFix f ha) = monoFix f ha) ∧
    (∀ {Z : Type*} (z : Z) (op : Z → Z),
      ∃! s : ℕ → Z, s 0 = z ∧ ∀ n, s (n + 1) = op (s n)) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element)
      {a : V.Element} (ha : f a ≤ a) {y : V.Element},
      f y = y → monoFix f ha ≤ y) ∧
    (∀ {s : ℕ → ℕ}, s 0 = 0 → (∀ n, s (n + 1) = s n + 1) → ∀ n, s n = n) :=
  ⟨@monoFix_isFixed, @exists_unique_nat_rec, @monoFix_least, @nat_iterate_unique⟩

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
