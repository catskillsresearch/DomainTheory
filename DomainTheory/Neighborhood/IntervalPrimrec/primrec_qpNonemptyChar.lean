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
import DomainTheory.Neighborhood.IntervalPrimrec.primrec_qpNonemptyBop


namespace DomainTheory.Neighborhood

open Domain.Recursive








































theorem primrec_qpNonemptyChar : Nat.Primrec qpNonemptyChar := by
  have hg : Nat.Primrec (fun t : ℕ => qpNonemptyBop t.unpair.1) :=
    primrec_qpNonemptyBop.comp Nat.Primrec.left
  exact ((primrec_existsListChar hg).comp (primrec_id.pair (Nat.Primrec.const 0))).of_eq
    fun c => by
      unfold qpNonemptyChar
      simp only [id, unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood
