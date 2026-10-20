/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise724.Basic


namespace DomainTheory.Neighborhood.Exercise724

open NeighborhoodSystem Domain.Recursive
















































theorem Lenum_subset_char_eq_one_iff (n m : ℕ) :
    Lenum n ⊆ Lenum m ↔ LenumSubsetChar (Nat.pair n m) = 1 := by
  unfold LenumSubsetChar
  rw [unpair_pair_fst, unpair_pair_snd, Lenum_subset_iff]

end DomainTheory.Neighborhood.Exercise724
