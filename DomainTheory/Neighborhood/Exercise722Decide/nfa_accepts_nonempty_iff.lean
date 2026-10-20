/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722DFA
import DomainTheory.Neighborhood.Exercise722Cat
import DomainTheory.Neighborhood.Exercise722Words
import DomainTheory.Neighborhood.Exercise722Decide.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}














variable {σ : Type}

/-- A nonempty accepted language ⟺ some accept state is reachable by reading some word. -/
theorem nfa_accepts_nonempty_iff (M : NFA Bool σ) :
    M.accepts.Nonempty ↔ ∃ s ∈ M.accept, ∃ x, s ∈ M.eval x := by
  constructor
  · rintro ⟨x, S, hS, hSe⟩; exact ⟨S, hS, x, hSe⟩
  · rintro ⟨S, hS, x, hSe⟩; exact ⟨x, S, hS, hSe⟩

end Exercise722
end DomainTheory.Neighborhood
