/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Data.List.Infix
import DomainTheory.Neighborhood.ExampleB.Basic
import DomainTheory.Neighborhood.ExampleB.prepend_mono
import DomainTheory.Neighborhood.ExampleB.prepend_append


namespace DomainTheory.Neighborhood.ExampleB

open DomainTheory.Neighborhood NeighborhoodSystem























/-- **`σ` and `τ` prepend in sequence, like concatenation.** `(στ)x = σ(τx)`: applying the
prefix `σ ++ τ` in one step agrees with applying `τ` first and then `σ`. (Used in Exercise 2.16's
second half — the uniqueness of the parity map — to unfold `f(σ₁σ₂ … σₙx)` one token at a time.) -/
theorem sigmaElt_append (σ τ : Str) (x : B.Element) :
    sigmaElt (σ ++ τ) x = sigmaElt σ (sigmaElt τ x) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    refine ⟨hY, prepend τ X, ⟨memB_prepend τ (x.sub hX), X, hX, subset_rfl⟩, ?_⟩
    rw [prepend_append]; exact hsub
  · rintro ⟨hY, X, ⟨_, X', hX', hsub'⟩, hsub⟩
    refine ⟨hY, X', hX', ?_⟩
    rw [← prepend_append]
    exact (prepend_mono σ hsub').trans hsub

end DomainTheory.Neighborhood.ExampleB
