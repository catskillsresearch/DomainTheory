/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.triangle_eq_zero


namespace DomainTheory.DataTypesAsLattices





































theorem pair_eq_right {n m : ℕ} (h : pair n m = m) : n = 0 ∧ m = 0 := by
  have : triangle (n + m) = 0 := by
    have h' : triangle (n + m) + m = m := by simpa [pair_eq_triangle] using h
    omega
  have : n + m = 0 := triangle_eq_zero this
  omega

end DomainTheory.DataTypesAsLattices
