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


namespace DomainTheory.DataTypesAsLattices











/-- **Scott 1976, Theorem 5.5.** `V(a)(x) = a(x)` for every `x` implies
`a` is expansive and idempotent on values, hence a closure once `a` is
already a graph retract. -/
theorem Vapply_eq_imp_expansive {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    x ⊆ funOf a x :=
  (h x) ▸ eq_5_16 a x

end DomainTheory.DataTypesAsLattices
