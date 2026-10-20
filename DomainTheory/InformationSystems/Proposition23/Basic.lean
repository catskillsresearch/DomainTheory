/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Definition22

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
