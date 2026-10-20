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













































































































































































/-- `Nat.max n 1` is primitive recursive. -/
theorem primrec_max_one : Nat.Primrec (fun n => Nat.max n 1) := by
  refine (primrec_selectFn (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))
    (Nat.Primrec.const 1) primrec_id).of_eq fun n => by
    unfold selectFn isOne Nat.max
    rcases n with _ | n <;> simp

end Domain.Recursive
