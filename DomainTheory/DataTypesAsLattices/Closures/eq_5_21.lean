/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_1
import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_rev
import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.21).** `a ⊆ V(a)`. -/
theorem eq_5_21 (a : Pomega) : a ⊆ funOf Vcomb a := by
  rw [Vcomb_app]
  exact (eq_5_1 a).trans (xi_star fun x => eq_5_18_rev a x)

end DomainTheory.DataTypesAsLattices
