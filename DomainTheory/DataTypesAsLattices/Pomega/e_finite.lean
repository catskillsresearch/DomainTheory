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


namespace DomainTheory.DataTypesAsLattices












theorem e_finite (n : ℕ) : (e n).Finite :=
  (Finset.range (n + 1)).finite_toSet.subset fun _k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_e_le hk))

end DomainTheory.DataTypesAsLattices
