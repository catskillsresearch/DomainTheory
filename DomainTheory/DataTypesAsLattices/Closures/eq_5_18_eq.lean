/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_18
import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_rev


namespace DomainTheory.DataTypesAsLattices











/-- **Scott 1976, (5.18).** Closures are fixed by `V` on values. -/
theorem eq_5_18_eq {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x = funOf a x :=
  subset_antisymm (eq_5_18 ha x) (eq_5_18_rev a x)

end DomainTheory.DataTypesAsLattices
