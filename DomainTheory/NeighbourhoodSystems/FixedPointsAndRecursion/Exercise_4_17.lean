module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.genSubmonoid

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

theorem example_417 :
    (∃ x y : Set ℕ, F 1 1 x = x ∧ F 1 1 y = y ∧ x ≠ y) ∧
    (∀ {S : Type*} [Monoid S] (a b : S),
      lfpSet (F a b) = (Submonoid.closure ({a, b} : Set S) : Set S)) :=
  ⟨fixedPoint_not_unique, @lfpSet_eq_closure⟩

end DomainTheory.NeighbourhoodSystems
