/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.LevelSetPrimrec
import DomainTheory.Neighborhood.MinLevel
import DomainTheory.Neighborhood.SplitV.Basic
import DomainTheory.Neighborhood.SplitV.primrec_myFirstBit
import DomainTheory.Neighborhood.SplitV.primrec_splitVMinLevel
import DomainTheory.Neighborhood.SplitV.primrec_splitVUpsampled


namespace DomainTheory.Neighborhood

open Domain.Recursive




















theorem primrec_splitVBit : Nat.Primrec splitVBit := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hbound : Nat.Primrec (fun n : ℕ => (2 : ℕ) ^ (splitVMinLevel n + 1)) :=
    primrec_two_pow hk1
  exact (primrec_myFirstBit.comp (primrec_splitVUpsampled.pair hbound)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

end DomainTheory.Neighborhood
