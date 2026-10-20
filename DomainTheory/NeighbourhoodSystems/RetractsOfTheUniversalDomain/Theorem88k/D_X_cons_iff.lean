/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88j.Basic
public import DomainTheory.Neighborhood.Theorem88j.D_X_mem
public import DomainTheory.Neighborhood.Theorem88j.D_X_of_diagFixed
public import DomainTheory.Neighborhood.Theorem88j.D_X_surj
public import DomainTheory.Neighborhood.Theorem88k.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

/-- **The one genuine lemma of Theorem 8.8(c), Part 4 of 6.** `D`-consistency of two list-codes
(`∃ k, D_X k ⊆ D_X c₁ ∩ D_X c₂`) is equivalent to plain `V`-consistency of the underlying raw
`myFoldCode` indices. -/
theorem D_X_cons_iff {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c₁ c₂ : ℕ) :
    (∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) ↔
      (∃ k, P.X k ⊆ P.X (myFoldCode P qChar cons c₁) ∩ P.X (myFoldCode P qChar cons c₂)) := by
  set n₁ := myFoldCode P qChar cons c₁ with hn₁
  set n₂ := myFoldCode P qChar cons c₂ with hn₂
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨myFoldCode P qChar cons k, hk⟩
  · rintro ⟨k, hk⟩
    have hn1 : DiagFixed P a n₁ := diagFixed_myFoldCode P qChar cons hqChar hcons c₁
    have hn2 : DiagFixed P a n₂ := diagFixed_myFoldCode P qChar cons hqChar hcons c₂
    have hVmem : V.mem (P.X n₁ ∩ P.X n₂) := by
      rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
    have hfix : (fixedNbhd a).mem (P.X n₁ ∩ P.X n₂) :=
      (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a n₁).mp hn1)
        ((diagFixed_iff_fixedNbhd_mem P a n₂).mp hn2) hVmem
    have hm : DiagFixed P a (P.inter n₁ n₂) := by
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]; exact hfix
    obtain ⟨c, hc⟩ := D_X_of_diagFixed hqChar hcons hm
    have heq : D_X P qChar cons c = D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ := by
      rw [hc, P.inter_spec ⟨k, hk⟩]
      unfold D_X
      rw [← hn₁, ← hn₂]
    exact ⟨c, heq ▸ subset_rfl⟩

end DomainTheory.Neighborhood
