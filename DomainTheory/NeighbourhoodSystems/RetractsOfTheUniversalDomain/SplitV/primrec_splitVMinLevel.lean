/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.LevelSetPrimrec
public import DomainTheory.Neighborhood.MinLevel
public import DomainTheory.Neighborhood.SplitV.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive















theorem primrec_splitVMinLevel : Nat.Primrec splitVMinLevel := by
  have hk : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.1) :=
    Nat.Primrec.left.comp primrec_canonIdx
  have hm : Nat.Primrec (fun n : ℕ => (canonIdx n).unpair.2) :=
    Nat.Primrec.right.comp primrec_canonIdx
  exact (primrec_minLevel.comp (hk.pair hm)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd]; rfl

end DomainTheory.Neighborhood
