/-ai
The nondeterministic automaton built from a deterministic automaton accepts the same language as the deterministic automaton.

Extend by a word. If the nondeterministic automaton accepts it, the evaluation lemma says the reached set is the singleton of the deterministic evaluation, so that state is accepting for the deterministic automaton. Conversely, if the deterministic automaton accepts the word, its evaluation state is accepting and, by the same lemma, lies in the singleton reached by the nondeterministic automaton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.dfaToNFA_eval

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- Choice-free version of `DFA.toNFA_correct`. -/
theorem dfaToNFA_accepts {σ : Type} (M : DFA Bool σ) : M.toNFA.accepts = M.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSe⟩
    rw [dfaToNFA_eval, Set.mem_singleton_iff] at hSe
    rw [DFA.mem_accepts, ← hSe]
    exact hS
  · intro hx
    rw [DFA.mem_accepts] at hx
    exact ⟨M.eval x, hx, by rw [dfaToNFA_eval]; exact Set.mem_singleton _⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
