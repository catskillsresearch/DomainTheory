/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import DomainTheory.DataTypesAsLattices.Pomega.Basic
import DomainTheory.DataTypesAsLattices.Pomega.e_zero
import DomainTheory.DataTypesAsLattices.Pomega.e_pow2
import DomainTheory.DataTypesAsLattices.Pomega.e_or


namespace DomainTheory.DataTypesAsLattices














theorem e_codeList (ks : List ℕ) : e (codeList ks) = {k | k ∈ ks} := by
  induction ks with
  | nil => simp [codeList, e_zero]
  | cons k ks ih =>
    ext i
    simp [codeList, e_or, e_pow2, ih]

end DomainTheory.DataTypesAsLattices
