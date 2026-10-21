/-ai
The bound autStateCard e equals the number of states of the automaton of e.

The proof is by induction on the expression. For the universal language the state type is a singleton, so both sides equal one. For a singleton word the state type is an optional initial segment one longer than the word, and the option and finite-segment counting formulas give the length plus two. For an intersection the inductive hypotheses and the product counting formula give the product of the bounds. For a concatenation they give the sum of the bounds.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autStateCard
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

theorem autStateCard_eq_card (e : SExpr) : autStateCard e = Fintype.card (autState e) := by
  induction e with
  | sigma =>
    simp [autStateCard, autState]
    exact (Fintype.card_unique (α := Unit)).symm
  | single σ =>
    simp only [autStateCard, autState]
    have h1 : Fintype.card (Option (Fin (σ.length + 1))) =
        Fintype.card (Fin (σ.length + 1)) + 1 :=
      Fintype.card_option (α := Fin (σ.length + 1))
    have h2 : Fintype.card (Fin (σ.length + 1)) = σ.length + 1 :=
      Fintype.card_fin (σ.length + 1)
    calc autStateCard (.single σ)
        = σ.length + 2 := rfl
      _ = (σ.length + 1) + 1 := rfl
      _ = Fintype.card (Fin (σ.length + 1)) + 1 := (congrArg (fun n => n + 1) h2).symm
      _ = Fintype.card (Option (Fin (σ.length + 1))) := h1.symm
  | cap a b ih_a ih_b =>
    simp [autStateCard, autState, ih_a, ih_b]
    exact (Fintype.card_prod (autState a) (autState b)).symm
  | cat a b ih_a ih_b =>
    simp [autStateCard, autState, ih_a, ih_b]
    exact (Fintype.card_sum (α := autState a) (β := autState b)).symm

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
