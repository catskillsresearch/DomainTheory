/-ai
The bound autStateCard e is at most the number of states of the automaton of e.

The proof is by induction on the expression. For the universal language the unique counting formula is at least the bound. For a singleton word the option and finite-segment formulas give equality with the bound, and equality yields the inequality. For an intersection the product of the inductive inequalities is at most the product of the numbers of states. For a concatenation the sum of the inductive inequalities is at most the sum of the numbers of states.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}











theorem autStateCard_le_card (e : SExpr) : autStateCard e ≤ Fintype.card (autState e) := by
  induction e with
  | sigma =>
    simp [autStateCard, autState]
    exact (Fintype.card_unique (α := Unit)).ge
  | single σ =>
    have heq : autStateCard (.single σ) = Fintype.card (autState (.single σ)) := by
      simp only [autStateCard, autState]
      have h1 : Fintype.card (Option (Fin (σ.length + 1))) =
          Fintype.card (Fin (σ.length + 1)) + 1 :=
        Fintype.card_option (α := Fin (σ.length + 1))
      have h2 : Fintype.card (Fin (σ.length + 1)) = σ.length + 1 :=
        Fintype.card_fin (σ.length + 1)
      calc σ.length + 2
          = (σ.length + 1) + 1 := rfl
        _ = Fintype.card (Fin (σ.length + 1)) + 1 := (congrArg (fun n => n + 1) h2).symm
        _ = Fintype.card (Option (Fin (σ.length + 1))) := h1.symm
    exact Nat.le_of_eq heq
  | cap a b ih_a ih_b =>
    simp only [autStateCard, autState]
    exact (Nat.mul_le_mul ih_a ih_b).trans (Fintype.card_prod (autState a) (autState b)).ge
  | cat a b ih_a ih_b =>
    simp only [autStateCard, autState]
    exact (Nat.add_le_add ih_a ih_b).trans (Fintype.card_sum (α := autState a) (β := autState b)).ge

end Exercise722
end DomainTheory.NeighbourhoodSystems
