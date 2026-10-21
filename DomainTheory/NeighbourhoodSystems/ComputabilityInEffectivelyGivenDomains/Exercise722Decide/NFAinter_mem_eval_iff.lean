/-ai
A pair of states is reached by the product automaton on a word if and only if each component is reached by its own automaton on that word.

The proof inducts on the word from the right. On the empty word the start clauses agree. Extending by a letter, a product predecessor splits into component predecessors whose letter steps are the two components of the product step, and a pair of component steps reassembles into one product step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

section NFAinterLemmas

variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

theorem NFAinter_mem_eval_iff (x : List Bool) (p : σ₁ × σ₂) :
    p ∈ (NFAinter M₁ M₂).eval x ↔ p.1 ∈ M₁.eval x ∧ p.2 ∈ M₂.eval x := by
  induction x using List.reverseRecOn generalizing p with
  | nil => exact Iff.rfl
  | append_singleton x a ih =>
    rw [NFA.eval_append_singleton, NFA.mem_stepSet]
    constructor
    · rintro ⟨q, hq, hstep⟩
      rw [ih] at hq
      rw [NFA.eval_append_singleton, NFA.mem_stepSet, NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨⟨q.1, hq.1, hstep.1⟩, ⟨q.2, hq.2, hstep.2⟩⟩
    · rintro ⟨h1, h2⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at h1 h2
      obtain ⟨q1, hq1, hs1⟩ := h1
      obtain ⟨q2, hq2, hs2⟩ := h2
      exact ⟨(q1, q2), (ih (q1, q2)).mpr ⟨hq1, hq2⟩, hs1, hs2⟩

end NFAinterLemmas

end Exercise722

end DomainTheory.NeighbourhoodSystems
