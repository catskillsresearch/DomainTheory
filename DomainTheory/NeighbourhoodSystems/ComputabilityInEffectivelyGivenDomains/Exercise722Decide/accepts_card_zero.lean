/-ai
An automaton whose state type has cardinality zero accepts no word.

An accepted word would yield a start state and a run to an accept state, but a type of cardinality zero has no element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
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

theorem accepts_card_zero (hσ : Fintype.card σ = 0) {w : List Bool} (hw : w ∈ M.accepts) : False := by
  rw [NFA.mem_accepts] at hw
  obtain ⟨t, ht, hte⟩ := hw
  rw [NFA.mem_evalFrom_iff_exists (S := M.start) (s := t) (x := w)] at hte
  obtain ⟨s, hs, _⟩ := hte
  exact (Fintype.card_eq_zero_iff.mp hσ).elim s

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
