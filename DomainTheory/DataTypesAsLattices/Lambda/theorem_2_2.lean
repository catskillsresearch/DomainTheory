/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_beta
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_xi
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_alpha


namespace DomainTheory.DataTypesAsLattices














/-- **Scott 1976, Theorem 2.2 (The conversion theorem).**
The three basic principles (α), (β), (ξ) are valid in the model. -/
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    (∀ j, (∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) →
        interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ) ∧
      funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) ∧
        ∀ σ, (∀ v, interp body (envSet ρ i v) = interp σ (envSet ρ i v)) →
          interp (.lam i body) ρ = interp (.lam i σ) ρ :=
  ⟨fun j h => theorem_2_2_alpha i j body ρ h,
    theorem_2_2_beta i body ρ y,
    fun _σ h => theorem_2_2_xi h⟩

end DomainTheory.DataTypesAsLattices
