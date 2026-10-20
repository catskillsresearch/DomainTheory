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











/-- **Scott 1976, (5.16).** `x ⊆ V(a)(x)`. -/
theorem eq_5_16 (a x : Pomega) : x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.1 hk

end DomainTheory.DataTypesAsLattices
