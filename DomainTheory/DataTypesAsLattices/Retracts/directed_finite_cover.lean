/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices





































theorem directed_finite_cover {A : Set (Fixpoints f)}
    (hA : IsDirectedSet A) {t : Pomega} (ht : t.Finite)
    (hsub : t ⊆ ⋃₀ (Fixpoints.vals A)) :
    ∃ z ∈ A, t ⊆ z := by
  classical
  have aux : ∀ s : Finset ℕ,
      (s : Set ℕ) ⊆ ⋃₀ (Fixpoints.vals A) →
        ∃ z ∈ A, (s : Set ℕ) ⊆ z := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        obtain ⟨z, hz⟩ := hA.1
        exact ⟨z, hz, by simp⟩
    | insert k s hks ih =>
        intro hs
        obtain ⟨u, hu, hsu⟩ :=
          ih (fun m hm => hs (by simp [hm]))
        obtain ⟨v, hv, hkv⟩ :=
          Set.mem_sUnion.mp
            (hs (show k ∈ (insert k s : Finset ℕ) by simp))
        obtain ⟨v', hv'A, rfl⟩ := hv
        obtain ⟨z, hz, huz, hvz⟩ := hA.2 hu hv'A
        refine ⟨z, hz, ?_⟩
        intro m hm
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hm
        rcases hm with rfl | hm
        · exact hvz hkv
        · exact huz (hsu hm)
  obtain ⟨z, hzA, hz⟩ := aux ht.toFinset (by simpa using hsub)
  exact ⟨z, hzA, fun m hm => hz (by simpa using hm)⟩

end DomainTheory.DataTypesAsLattices
