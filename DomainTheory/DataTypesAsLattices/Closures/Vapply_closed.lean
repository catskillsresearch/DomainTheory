/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
import DomainTheory.DataTypesAsLattices.Closures.Vapply_prefixpoint


namespace DomainTheory.DataTypesAsLattices


















/-- **Scott 1976, Theorem 5.6 / (5.15).** The universe applied to `x` is
closed under `a` and contains `x`. -/
theorem Vapply_closed (a x : Pomega) :
    x ∪ funOf a (Vapply a x) ⊆ Vapply a x := by
  intro k hk
  rcases hk with hk | hk
  · exact eq_5_16 a x hk
  · exact (Vapply_prefixpoint a x).2 hk

end DomainTheory.DataTypesAsLattices
