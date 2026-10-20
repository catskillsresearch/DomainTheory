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


















/-- **Scott 1976, (5.11).** Closures act as expansive maps. -/
theorem eq_5_11 {a b u x : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    funOf u x ⊆ funOf b (funOf u (funOf a x)) := by
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have hy : funOf u (funOf a x) ⊆ funOf b (funOf u (funOf a x)) := by
    have := funOf_monotone_left hb.1 (funOf u (funOf a x))
    rwa [Icomb_app] at this
  exact subset_trans (funOf_monotone_right u hx) hy

end DomainTheory.DataTypesAsLattices
