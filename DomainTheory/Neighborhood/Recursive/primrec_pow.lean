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
import DomainTheory.Neighborhood.Recursive.recPow_eq


namespace Domain.Recursive



















































































/-- **Exponentiation is primitive recursive** (`unpaired (b, e) ↦ b ^ e`), choice-free. -/
theorem primrec_pow : Nat.Primrec (Nat.unpaired fun b e => b ^ e) := by
  have hg : Nat.Primrec (fun w => w.unpair.2.unpair.2 * w.unpair.1) :=
    primrec_mul₂ (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  refine (Nat.Primrec.prec (Nat.Primrec.const 1) hg).of_eq (fun p => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact recPow_eq p.unpair.1 p.unpair.2

end Domain.Recursive
