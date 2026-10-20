/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_17


namespace DomainTheory.DataTypesAsLattices











theorem Vapply_eq_imp_idem {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := eq_5_17 a x
  rwa [h (Vapply a x), h x] at this

end DomainTheory.DataTypesAsLattices
