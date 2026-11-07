module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.orderFixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

theorem example_421 :
    (∀ (s : ℕ → Set ℕ), s 0 = Set.univ →
      (∀ m, s (m + 1) = succImage (s m)) → s = upSet) ∧
    (∀ {u : Set (ℕ × ℕ)}, leOp u = u → u = leRel) ∧
    (leOp leRel = leRel) ∧
    (∀ (n : ℕ), lfpSet (mulOp n) = {k | ∃ i, k = n * i}) :=
  ⟨upSet_unique, @leOp_unique, leRel_isFixed, mulOp_lfp_eq_multiples⟩

end DomainTheory.NeighbourhoodSystems
