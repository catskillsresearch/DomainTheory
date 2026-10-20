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
import DomainTheory.Neighborhood.IntervalPrimrec.primrec_diffSingleCode


namespace DomainTheory.Neighborhood

open Domain.Recursive




























theorem primrec_diffAllStep : Nat.Primrec diffAllStep := by
  unfold diffAllStep
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hq : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  exact (primrec_diffSingleCode.comp (hacc.pair hq)).of_eq fun w => by
    simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood
