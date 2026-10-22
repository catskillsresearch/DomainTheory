/-ai
If two deterministic automata accept the denotations of two expressions, their product automaton accepts the denotation of the intersection expression.

Rewrite by the denotation of intersection and the two hypotheses. A word is accepted by the product when its product evaluation lies in the product accept set, and componentwise evaluation rewrites that membership as the pair of the two component evaluations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.inter_eval

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


/-- If `M₁`, `M₂` recognise `denote a`, `denote b`, their product DFA recognises `denote (a ∩ b)`. -/
theorem interDFA_accepts {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂)
    (a b : SExpr) (h₁ : M₁.accepts = denote a) (h₂ : M₂.accepts = denote b) :
    (M₁.inter M₂).accepts = denote (.cap a b) := by
  rw [denote_cap, ← h₁, ← h₂]
  ext w
  constructor
  · intro hw
    have hp : (M₁.inter M₂).eval w ∈ (M₁.inter M₂).accept := hw
    rw [inter_eval] at hp
    exact hp
  · intro hw
    show (M₁.inter M₂).eval w ∈ (M₁.inter M₂).accept
    rw [inter_eval]
    exact hw

end Exercise722
end DomainTheory.NeighbourhoodSystems
