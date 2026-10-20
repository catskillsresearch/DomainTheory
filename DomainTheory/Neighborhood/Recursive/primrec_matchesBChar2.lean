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
import DomainTheory.Neighborhood.Recursive.primrec_fuelTable
import DomainTheory.Neighborhood.Recursive.primrec_matchesBCharBodyLookup
import DomainTheory.Neighborhood.Recursive.matchesBChar_fuelTable_eq


namespace Domain.Recursive

















































































































































































































































open DomainTheory.Neighborhood Exercise722

































/-- **`matchesBChar` is jointly primitive recursive in `(fuel, sexprCode, wordCode)`.** -/
theorem primrec_matchesBChar2 :
    Nat.Primrec (fun s => matchesBChar s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2) := by
  have hft := primrec_fuelTable primrec_matchesBCharBodyLookup
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable matchesBCharBodyLookup s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable matchesBCharBodyLookup s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (Nat.Primrec.pair hcomp (Nat.Primrec.pair Nat.Primrec.right (Nat.Primrec.const 0)))).of_eq
      fun s => by simp
  exact hnth.of_eq fun s => by
    rw [matchesBChar_fuelTable_eq s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)]

end Domain.Recursive
