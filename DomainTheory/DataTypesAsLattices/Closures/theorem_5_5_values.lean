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
import DomainTheory.DataTypesAsLattices.Closures.eq_5_17


namespace DomainTheory.DataTypesAsLattices











/-- **Scott 1976, Theorem 5.5 (partial).** `V(a)` is always a closure of `x`,
and `V` fixes exactly the closure operations in the sense of (5.18) on values. -/
theorem theorem_5_5_values (a x : Pomega) :
    x ⊆ Vapply a x ∧ Vapply a (Vapply a x) = Vapply a x :=
  ⟨eq_5_16 a x, eq_5_17 a x⟩

end DomainTheory.DataTypesAsLattices
