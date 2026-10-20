/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic


namespace Domain.Recursive

















































































































































































































































open DomainTheory.Neighborhood Exercise722
































theorem primrec_matchesBCatGLookup : Nat.Primrec matchesBCatGLookup := by
  have hi : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hcw : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have ha : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb : Nat.Primrec (fun w => w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have htake : Nat.Primrec (fun w => takeCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2) :=
    (primrec_takeCode.comp (Nat.Primrec.pair hi hcw)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hdrop : Nat.Primrec (fun w => dropCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2) :=
    (primrec_dropCode.comp (Nat.Primrec.pair hi hcw)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h1 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.1
        (takeCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2)) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.pair ha htake) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.2.unpair.1.unpair.2.unpair.2
        (dropCode w.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2)) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair Nat.Primrec.left
      (Nat.Primrec.pair (Nat.Primrec.pair hb hdrop) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mul₂ h1 h2).of_eq fun w => by
    dsimp [matchesBCatGLookup, matchesBCatG, mulBit]

end Domain.Recursive
