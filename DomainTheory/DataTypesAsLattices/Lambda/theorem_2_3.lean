/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.curryFin_app


namespace DomainTheory.DataTypesAsLattices



















/-- **Scott 1976, Theorem 2.3 (The reduction theorem).**
Any continuous function of `k` variables is represented by an element
`u ∈ Pω` via iterated application. -/
theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs :=
  ⟨curryFin f, curryFin_app hf⟩

end DomainTheory.DataTypesAsLattices
