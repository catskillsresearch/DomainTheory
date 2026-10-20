/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.LevelSetPrimrec
import DomainTheory.Neighborhood.MinLevel
import DomainTheory.Neighborhood.SplitV.Basic
import DomainTheory.Neighborhood.SplitV.primrec_myClearBit
import DomainTheory.Neighborhood.SplitV.primrec_splitVMinLevel
import DomainTheory.Neighborhood.SplitV.primrec_splitVUpsampled
import DomainTheory.Neighborhood.SplitV.primrec_splitVBit


namespace DomainTheory.Neighborhood

open Domain.Recursive






















theorem primrec_splitVRight : Nat.Primrec splitVRight := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hclear : Nat.Primrec (fun n : ℕ => myClearBit (splitVUpsampled n) (splitVBit n)) :=
    (primrec_myClearBit.comp (primrec_splitVUpsampled.pair primrec_splitVBit)).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (Nat.Primrec.pair hk1 hclear).of_eq fun n => rfl

end DomainTheory.Neighborhood
