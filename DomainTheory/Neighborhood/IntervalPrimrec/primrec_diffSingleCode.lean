/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition87
import DomainTheory.Neighborhood.RationalPrimrec
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.IntervalPrimrec.Basic
import DomainTheory.Neighborhood.IntervalPrimrec.primrec_diffOneCode


namespace DomainTheory.Neighborhood

open Domain.Recursive

























theorem primrec_diffSingleCode : Nat.Primrec (fun t : ℕ => diffSingleCode t.unpair.1 t.unpair.2) := by
  unfold diffSingleCode
  exact ((primrec_flatMapCode primrec_diffOneCode).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood
