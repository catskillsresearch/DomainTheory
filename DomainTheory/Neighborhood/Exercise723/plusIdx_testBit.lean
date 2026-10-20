/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic
import DomainTheory.Neighborhood.Exercise723.testBit_orUpTo_self


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

























theorem plusIdx_testBit (n m k : ℕ) :
    (plusIdx n m).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true :=
  testBit_orUpTo_self n m k

end DomainTheory.Neighborhood.Exercise723
