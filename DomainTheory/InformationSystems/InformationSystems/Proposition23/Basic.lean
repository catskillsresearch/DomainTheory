/-ai
This file gathers and re-exports constructive finset operations and set-level entailment. Scott's Proposition 2.3 states that the empty set entails the singleton of the least token, that set-level entailment of v by a consistent u puts their union among the consistent sets, that set-level entailment is reflexive, transitive, and monotone, and that it is closed under union of the entailed sets.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22

@[expose] public section

/-!
# Proposition 2.3 — elementary properties of set-level entailment

**Scott 1982, Proposition 2.3.** For all `u, v, w, u', v' ∈ Con`:
(i) `∅ ⊢ {Δ}`; (ii) `u ⊢ v ⇒ u ∪ v ∈ Con`; (iii) `u ⊢ u`;
(iv) transitivity; (v) monotonicity; (vi) `u ⊢ v ∧ u ⊢ v' ⇒ u ⊢ v ∪ v'`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)
end InfoSys
end DomainTheory.InformationSystems
