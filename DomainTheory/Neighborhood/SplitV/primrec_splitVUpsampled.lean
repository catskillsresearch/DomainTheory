/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.LevelSetPrimrec
import DomainTheory.Neighborhood.MinLevel
import DomainTheory.Neighborhood.SplitV.Basic
import DomainTheory.Neighborhood.SplitV.primrec_splitVMinLevel
import DomainTheory.Neighborhood.SplitV.primrec_splitVMinMask


namespace DomainTheory.Neighborhood

open Domain.Recursive



















theorem primrec_splitVUpsampled : Nat.Primrec splitVUpsampled := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  exact (primrec_myUpsample.comp
      (primrec_splitVMinLevel.pair (hk1.pair primrec_splitVMinMask))).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

end DomainTheory.Neighborhood
