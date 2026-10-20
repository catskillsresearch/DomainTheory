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
import DomainTheory.DataTypesAsLattices.Pomega.e_or


namespace DomainTheory.DataTypesAsLattices













theorem e_or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by
  rw [e_or]
  exact Set.union_subset hn hm

end DomainTheory.DataTypesAsLattices
