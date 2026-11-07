module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's Exercise 1.21: consistency via brackets; token system complete and positive;
    toToken is bijective. -/
theorem exercise_1_21 :
    (∀ (X : ℕ → Set α) {n : ℕ}, (∀ i, i < n → V.mem (X i)) →
        (V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty)) ∧
      (∀ (X : ℕ → Set α) {n : ℕ}, (∀ i, i < n → V.mem (X i)) →
        (V.Consistent X n ↔ ∃ x, ∀ i, i < n → x ∈ V.bracket (X i))) ∧
      V.tokenSystem.IsComplete ∧
      V.tokenSystem.IsPositive ∧
      Function.Bijective V.toToken :=
  ⟨V.consistent_iff_bracket_interUpTo_nonempty, V.consistent_iff_iInter_bracket_nonempty,
    V.tokenSystem_complete, V.tokenSystem_isPositive, V.tokenSystem_toToken_bijective⟩
