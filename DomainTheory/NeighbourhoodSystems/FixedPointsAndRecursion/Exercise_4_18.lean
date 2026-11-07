module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.numberDomainCheck

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap NatDom

theorem example_418 :
    (∀ x : N.Element, x = N.bot ∨ ∃ n, x = natElem n) ∧
    (∀ {n m : ℕ}, natElem n = natElem m → n = m) ∧
    (∀ k : ℕ, natElem 0 ≠ natElem (k + 1)) ∧
    (∀ {n m : ℕ},
      succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m) → n = m) ∧
    (∀ n : ℕ, natElem 0 ≠ succMap.toElementMap (natElem n)) :=
  ⟨element_classification, @natElem_injective, natElem_zero_ne_succ,
    @succMap_injective, zero_ne_succMap⟩

end DomainTheory.NeighbourhoodSystems
