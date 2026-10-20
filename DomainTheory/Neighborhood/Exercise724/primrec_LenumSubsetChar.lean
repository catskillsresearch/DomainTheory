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
















































theorem primrec_LenumSubsetChar : Nat.Primrec LenumSubsetChar :=
  primrec_isPrefixChar_swap.of_eq fun t => by simp only [LenumSubsetChar]

end DomainTheory.Neighborhood.Exercise724
