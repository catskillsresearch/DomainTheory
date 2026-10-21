/-ai
The nondeterministic automaton obtained from a deterministic automaton evaluates a word to the singleton of the deterministic evaluation.

The proof reads the word from the end. The empty word is immediate. For a word extended by one symbol, the inductive hypothesis and membership in a step set reduce both directions to deterministic evaluation of an appended symbol, with the preceding state the deterministic evaluation of the shorter word.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- The NFA from a DFA tracks the single deterministic state as a singleton. -/
theorem dfaToNFA_eval {σ : Type} (M : DFA Bool σ) (x : List Bool) :
    M.toNFA.eval x = {M.eval x} := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x a ih =>
    rw [NFA.eval_append_singleton, ih]
    ext s
    rw [NFA.mem_stepSet]
    constructor
    · rintro ⟨t, ht, hs⟩
      rw [Set.mem_singleton_iff] at ht
      subst ht
      rw [Set.mem_singleton_iff, DFA.eval_append_singleton]
      exact hs
    · intro hs
      rw [Set.mem_singleton_iff, DFA.eval_append_singleton] at hs
      exact ⟨M.eval x, Set.mem_singleton _, hs⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
