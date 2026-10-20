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
import DomainTheory.Neighborhood.Recursive.primrec_autStateCardFuelChar2
import DomainTheory.Neighborhood.Recursive.primrec_matchesBChar2
import DomainTheory.Neighborhood.Recursive.primrec_codeBound


namespace Domain.Recursive

















































































































































































































































open DomainTheory.Neighborhood Exercise722

















































theorem primrec_decideNonemptyBChar2 :
    Nat.Primrec (fun s => decideNonemptyBChar s.unpair.1 s.unpair.2) := by
  have hg : Nat.Primrec (fun u => mulBit (allBinDigitsChar u.unpair.2.unpair.1)
      (matchesBChar u.unpair.1 u.unpair.2.unpair.2 u.unpair.2.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair
      (primrec_allBinDigitsChar.comp (Nat.Primrec.left.comp Nat.Primrec.right))
      (primrec_matchesBChar2.comp (Nat.Primrec.pair Nat.Primrec.left
        (Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
          (Nat.Primrec.left.comp Nat.Primrec.right)))))).of_eq fun u => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hbe := primrec_bExistsFn_param hg
  have hpack : Nat.Primrec (fun s => Nat.pair (Nat.pair s.unpair.1 s.unpair.2)
      (codeBound (autStateCardFuelChar s.unpair.1 s.unpair.2))) :=
    Nat.Primrec.pair (Nat.Primrec.pair Nat.Primrec.left Nat.Primrec.right)
      (primrec_codeBound.comp primrec_autStateCardFuelChar2)
  exact (hbe.comp hpack).of_eq fun s => by
    simp only [unpair_pair_fst, unpair_pair_snd, decideNonemptyBChar]

end Domain.Recursive
