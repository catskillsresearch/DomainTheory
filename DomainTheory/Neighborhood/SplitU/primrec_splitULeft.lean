/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.primrec_clipLtListCode
import DomainTheory.Neighborhood.SplitU.primrec_splitMidCode


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem
















theorem primrec_splitULeft : Nat.Primrec splitULeft :=
  (primrec_clipLtListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitULeft, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood
