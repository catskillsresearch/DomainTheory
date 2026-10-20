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
import DomainTheory.DataTypesAsLattices.Pomega.pair_inj
import DomainTheory.DataTypesAsLattices.Pomega.pair_unpair


namespace DomainTheory.DataTypesAsLattices






















theorem unpair_pair (n m : ℕ) : unpair (pair n m) = (n, m) := by
  have h := pair_unpair (pair n m)
  exact Prod.ext (pair_inj h).1 (pair_inj h).2

end DomainTheory.DataTypesAsLattices
