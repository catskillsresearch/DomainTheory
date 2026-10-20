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
import DomainTheory.Neighborhood.SplitV.primrec_splitVBit


namespace DomainTheory.Neighborhood

open Domain.Recursive






















theorem primrec_splitVLeft : Nat.Primrec splitVLeft := by
  have hk1 : Nat.Primrec (fun n : ℕ => splitVMinLevel n + 1) :=
    Nat.Primrec.succ.comp primrec_splitVMinLevel
  have hpow : Nat.Primrec (fun n : ℕ => (2 : ℕ) ^ splitVBit n) := primrec_two_pow primrec_splitVBit
  exact (Nat.Primrec.pair hk1 hpow).of_eq fun n => rfl

end DomainTheory.Neighborhood
