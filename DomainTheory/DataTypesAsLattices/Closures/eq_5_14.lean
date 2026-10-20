/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.Vapply_eq_Vstep


namespace DomainTheory.DataTypesAsLattices




















/-- **Scott 1976, (5.14) = (5.15).** -/
theorem eq_5_14 (a x : Pomega) : VapplyY a x = Vapply a x := by
  have hfix : Vstep a x (VapplyY a x) = VapplyY a x :=
    (theorem_1_4 (Vstep_isScottContinuous a x)).1
  apply subset_antisymm
  · exact (theorem_1_4 (Vstep_isScottContinuous a x)).2 (Vapply a x)
      (Vapply_eq_Vstep a x).symm
  · intro k hk
    have hx : x ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inl hm
      rwa [hfix] at this
    have ha : funOf a (VapplyY a x) ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inr hm
      rwa [hfix] at this
    exact hk (VapplyY a x) ⟨hx, ha⟩

end DomainTheory.DataTypesAsLattices
