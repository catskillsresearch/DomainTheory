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
import DomainTheory.Neighborhood.Recursive.existsListStp_eq


namespace Domain.Recursive










































































































































theorem existsListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    existsListChar g p c
      = List.foldl (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) 0 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => existsListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) := by
    funext acc x; exact existsListStp_eq g acc x p
  unfold existsListChar; rw [foldCode_eq', hfun]

end Domain.Recursive
