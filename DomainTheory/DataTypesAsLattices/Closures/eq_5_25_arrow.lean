/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_25


namespace DomainTheory.DataTypesAsLattices


































theorem eq_5_25_arrow (hI : Icomb ⊆ arrowR dEq dEq) :
    dEq = arrowR dEq dEq := by
  apply subset_antisymm
  · nth_rw 1 [eq_5_25]
    exact Set.union_subset hI subset_rfl
  · nth_rw 3 [eq_5_25]
    exact Set.subset_union_right

end DomainTheory.DataTypesAsLattices
