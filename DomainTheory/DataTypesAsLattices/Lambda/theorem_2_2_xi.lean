/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices












/-- **Scott 1976, Theorem 2.2 (ξ).** -/
theorem theorem_2_2_xi {i : ℕ} {τ σ : Term} {ρ : ℕ → Pomega}
    (h : ∀ v, interp τ (envSet ρ i v) = interp σ (envSet ρ i v)) :
    interp (.lam i τ) ρ = interp (.lam i σ) ρ := by
  simp [interp, h]

end DomainTheory.DataTypesAsLattices
