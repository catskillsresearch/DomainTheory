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
import DomainTheory.Neighborhood.Exercise724.primrec_LenumSubsetChar
import DomainTheory.Neighborhood.Exercise724.LenumSubsetChar_le_one
import DomainTheory.Neighborhood.Exercise724.Lenum_subset_char_eq_one_iff


namespace DomainTheory.Neighborhood.Exercise724

open NeighborhoodSystem Domain.Recursive
















































/-- `isPrefixChar` gives a `RecDecidable₂` decider for `Lenum n ⊆ Lenum m`. -/
theorem Lenum_subset_recDecidable : RecDecidable₂ (fun n m => Lenum n ⊆ Lenum m) :=
  RecDecidable₂.of_paired_zero_one_char primrec_LenumSubsetChar
    (fun t => by have := LenumSubsetChar_le_one t; omega)
    Lenum_subset_char_eq_one_iff

end DomainTheory.Neighborhood.Exercise724
