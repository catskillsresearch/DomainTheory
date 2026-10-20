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



























































































































theorem primrec_mapPairStp : Nat.Primrec mapPairStp := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((h22.pair h1).pair h21)).of_eq (fun _ => rfl)

end Domain.Recursive
