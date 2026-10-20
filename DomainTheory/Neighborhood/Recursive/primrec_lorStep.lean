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
import DomainTheory.Neighborhood.Recursive.primrec_div2
import DomainTheory.Neighborhood.Recursive.primrec_lowOr


namespace Domain.Recursive































































































































theorem primrec_lorStep : Nat.Primrec lorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => lowOr s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec_lowOr.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

end Domain.Recursive
