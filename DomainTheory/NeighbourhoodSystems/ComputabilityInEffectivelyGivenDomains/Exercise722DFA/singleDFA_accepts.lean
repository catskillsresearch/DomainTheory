/-ai
The automaton for a single word accepts exactly the singleton of that word.

Evaluation from the start state is the prefix law. If the input is a prefix of the word, the resulting length equals the length of the word exactly when the input equals the word. If the input is not a prefix, evaluation is the sink, which is not the accept state, while equality with the word would make the input a prefix of itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.singleDFA_evalFrom

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability







/-- **The single-word DFA recognises exactly `{σ}`.** -/
theorem singleDFA_accepts (σ : List Bool) : (singleDFA σ).accepts = {σ} := by
  ext w
  show (singleDFA σ).evalFrom (some ⟨0, by omega⟩) w ∈ (singleDFA σ).accept ↔ _
  rw [singleDFA_evalFrom]
  by_cases h : w <+: List.drop (0 : ℕ) (σ : List Bool)
  · rw [dite_eq_left h, List.drop_zero] at *
    show some (⟨0 + w.length, _⟩ : Fin (σ.length + 1)) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff, Option.some.injEq, Fin.mk.injEq, Nat.zero_add]
    constructor
    · intro hlen; exact h.eq_of_length hlen
    · intro hw; subst hw; rfl
  · rw [dite_eq_right h, List.drop_zero] at *
    show (none : SingleState σ) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hcontra; exact absurd hcontra (by simp)
    · intro hw; subst hw; exact absurd List.prefix_rfl h

end Exercise722
end DomainTheory.NeighbourhoodSystems
