/-ai
The concatenation automaton places the first automaton on left summands and the second on right summands. A left state steps on a letter by the left copy of the first automaton's step, and on an epsilon transition to the right copies of the second automaton's start states when the left state is accepting. A right state steps on a letter by the right copy of the second automaton's step, and has no epsilon transition. The start states are the left copies of the first start states, and the accept states are the right copies of the second accept states.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.EpsilonNFA
import all Mathlib.Computability.EpsilonNFA

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- The concatenation `εNFA`: `M₁` on `inl`, `M₂` on `inr`, ε-edges from `M₁`-accept to `M₂`-start. -/
def catEps (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂) : εNFA Bool (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | inl s, some c => inl '' M₁.step s c
    | inl s, none   => {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start}
    | inr s, some c => inr '' M₂.step s c
    | inr _, none   => ∅
  start := inl '' M₁.start
  accept := inr '' M₂.accept

end Exercise722

end DomainTheory.NeighbourhoodSystems
