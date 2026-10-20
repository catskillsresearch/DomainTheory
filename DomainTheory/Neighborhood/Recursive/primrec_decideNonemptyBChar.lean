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
import DomainTheory.Neighborhood.Recursive.primrec_autStateCardFuelChar
import DomainTheory.Neighborhood.Recursive.primrec_matchesBChar
import DomainTheory.Neighborhood.Recursive.primrec_codeBound


namespace Domain.Recursive

















































































































































































































































open DomainTheory.Neighborhood Exercise722













































theorem primrec_decideNonemptyBChar (fuel : ℕ) :
    Nat.Primrec (fun c_e => decideNonemptyBChar fuel c_e) := by
  have hg : Nat.Primrec (fun w =>
      mulBit (allBinDigitsChar w.unpair.1) (matchesBChar fuel w.unpair.2 w.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair (primrec_allBinDigitsChar.comp Nat.Primrec.left)
      ((primrec_matchesBChar fuel).comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)))).of_eq
      fun w => by simp
  have hpack : Nat.Primrec (fun c_e =>
      Nat.pair c_e (codeBound (autStateCardFuelChar fuel c_e))) :=
    Nat.Primrec.pair Nat.Primrec.id
      (primrec_codeBound.comp (primrec_autStateCardFuelChar fuel))
  refine ((primrec_bExistsFn hg).comp hpack).of_eq fun c_e => ?_
  simp [decideNonemptyBChar]

end Domain.Recursive
