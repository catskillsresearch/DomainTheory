/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Regular
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option
import DomainTheory.Neighborhood.Exercise722DFA.Basic
import DomainTheory.Neighborhood.Exercise722DFA.inter_eval


namespace DomainTheory.Neighborhood

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
end DomainTheory.Neighborhood
