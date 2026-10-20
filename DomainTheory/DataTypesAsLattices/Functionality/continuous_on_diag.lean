/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices














/-- Diagonal continuity, packaged from Theorem 1.3. -/
theorem continuous_on_diag {F : Pomega → Pomega → Pomega}
    (h1 : ∀ y, IsScottContinuous (fun x => F x y))
    (h2 : ∀ x, IsScottContinuous (fun y => F x y)) :
    IsScottContinuous (fun x => F x x) := by
  intro x
  have H := theorem_1_3_diag (x := x) (f := F) h1 h2
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ F (e n) (e n)} := by rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ x ∧ k ∈ F (e n) (e n)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

end DomainTheory.DataTypesAsLattices
