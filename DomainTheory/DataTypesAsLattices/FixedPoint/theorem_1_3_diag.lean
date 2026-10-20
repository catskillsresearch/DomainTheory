/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Graph
import DomainTheory.DataTypesAsLattices.FixedPoint.Basic


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3 (The substitution theorem), binary case.**
If `f` is continuous in each argument separately, then `x ↦ f(x,x)` is
continuous. -/
theorem theorem_1_3_diag {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y))
    {x : Pomega} :
    f x x = ⋃ n, {k | e n ⊆ x ∧ k ∈ f (e n) (e n)} := by
  apply subset_antisymm
  · intro k hk
    have : k ∈ scottUnion (fun z => f z x) x := by
      rw [← hfx x x]; exact hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    have : k ∈ scottUnion (fun y => f (e n) y) x := by
      rw [← hfy (e n) x]; exact hkn
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    refine Set.mem_iUnion.mpr ⟨n ||| m, ?_⟩
    refine ⟨e_or_of_subset hn hm, ?_⟩
    have hle : e n ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_left
    have hre : e m ⊆ e (n ||| m) := by rw [e_or]; exact Set.subset_union_right
    exact isScottContinuous_monotone (hfy (e (n ||| m))) hre
      (isScottContinuous_monotone (hfx (e m)) hle hkm)
  · intro k hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp hk
    exact isScottContinuous_monotone (hfy x) hn
      (isScottContinuous_monotone (hfx (e n)) hn hkn)

end DomainTheory.DataTypesAsLattices
