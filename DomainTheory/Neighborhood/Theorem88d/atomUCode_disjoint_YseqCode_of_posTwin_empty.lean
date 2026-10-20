/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.deltaOf_mod_two_pow_of_lt
import DomainTheory.Neighborhood.Theorem88d.mem_UX_YseqCode_iff
import DomainTheory.Neighborhood.Theorem88d.eq_of_deltaOf_agree_of_lt_two_pow


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

























































/-- **General exclusion lemma**: if a bit-source `k'` is non-junk at depth `n`, and its own
canonical "positive twin" at depth `n + 1` (same bits below `n`, forcing bit `n` to `true`) is
junk, then `k'`'s own depth-`n` atom is disjoint from `YseqCode`'s entire union — no genuine
(non-junk) depth-`(n+1)` atom in the union can leak a point into it, whether that atom *is* `k'`'s
own excluded twin (immediate contradiction) or some *other* twin `i ≠ j` (disjoint at depth `n` by
`atomUCode_disjoint`, since distinct bit-sources below `2ⁿ` always disagree somewhere below `n`,
`eq_of_deltaOf_agree_of_lt_two_pow`). -/
theorem atomUCode_disjoint_YseqCode_of_posTwin_empty {n k' : ℕ} (hk' : atomUEmpty P n k' = 0)
    (hjunk : atomUEmpty P (n + 1) (k' % 2 ^ n + 2 ^ n) = 1) :
    UX (atomUCode P n k') ∩ UX (YseqCode P n) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzB, hzY⟩
  obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
  set j := k' % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k' (Nat.two_pow_pos n)
  have hk'j : ∀ l < n, deltaOf k' l = deltaOf j l := by
    intro l hl; rw [hjdef, deltaOf_mod_two_pow_of_lt hl]
  by_cases hij : i = j
  · rw [hij] at hie; exact absurd hie (by omega)
  · have hdisagree : ∃ l < n, deltaOf (i + 2 ^ n) l ≠ deltaOf k' l := by
      by_contra hcon
      push Not at hcon
      apply hij
      apply eq_of_deltaOf_agree_of_lt_two_pow hilt hjlt
      intro l hl
      have h1 : deltaOf (i + 2 ^ n) l = deltaOf i l := deltaOf_add_two_pow_of_lt _ hl
      have h2 := hcon l hl
      rw [h1] at h2
      exact h2.trans (hk'j l hl)
    obtain ⟨l, hl, hlne⟩ := hdisagree
    have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') = ∅ :=
      atomUCode_disjoint P n (i + 2 ^ n) k' (atomUEmpty_zero_of_succ P hie) hk' ⟨l, hl, hlne⟩
    have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode_subset P hie hz
    have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') := ⟨hzB', hzB⟩
    rw [hd] at hzmem
    exact absurd hzmem (Set.mem_empty_iff_false z).mp

end DomainTheory.Neighborhood
