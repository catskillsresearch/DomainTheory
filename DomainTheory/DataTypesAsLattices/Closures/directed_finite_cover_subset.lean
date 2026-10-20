/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices


















theorem directed_finite_cover_subset {f : Pomega → Pomega}
    {A : Set (Fixpoints f)} (hA : IsDirectedSubset A) {t : Pomega}
    (ht : t.Finite) (hsub : t ⊆ ⋃₀ (Subtype.val '' A)) :
    ∃ z ∈ A, t ⊆ z := by
  have hA' : IsDirectedSet A := by
    refine ⟨hA.1, ?_⟩
    intro x hx y hy
    obtain ⟨z, hz, hxz, hyz⟩ := hA.2 hx hy
    exact ⟨z, hz, hxz, hyz⟩
  simpa [Fixpoints.vals] using directed_finite_cover hA' ht (by
    simpa [Fixpoints.vals] using hsub)

end DomainTheory.DataTypesAsLattices
