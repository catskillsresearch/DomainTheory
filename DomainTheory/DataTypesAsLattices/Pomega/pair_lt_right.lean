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
import DomainTheory.DataTypesAsLattices.Pomega.pair_le_right


namespace DomainTheory.DataTypesAsLattices






















theorem pair_lt_right (n m : ℕ) : m < pair n m + 1 :=
  Nat.lt_succ_of_le (pair_le_right n m)

end DomainTheory.DataTypesAsLattices
