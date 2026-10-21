/-ai
The product automaton recognising an intersection has pairs of states. A pair steps on a letter, is a start state, or is an accept state exactly when both components do.
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

section NFAinterLemmas

/-- Product NFA recognising the intersection: states `σ₁ × σ₂`, stepping/starting/accepting
componentwise. -/
def NFAinter (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂) : NFA Bool (σ₁ × σ₂) where
  step s a := {t | t.1 ∈ M₁.step s.1 a ∧ t.2 ∈ M₂.step s.2 a}
  start := {s | s.1 ∈ M₁.start ∧ s.2 ∈ M₂.start}
  accept := {s | s.1 ∈ M₁.accept ∧ s.2 ∈ M₂.accept}

end NFAinterLemmas

end Exercise722

end DomainTheory.NeighbourhoodSystems
