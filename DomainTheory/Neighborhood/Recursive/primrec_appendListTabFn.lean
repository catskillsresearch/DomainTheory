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











































































































































































































































theorem primrec_appendListTabFn : Nat.Primrec appendListTabFn := by
  have hi := Nat.Primrec.left
  have hp := Nat.Primrec.right
  have hlen1 := Nat.Primrec.right.comp (Nat.Primrec.right.comp hp)
  have hc1 := Nat.Primrec.left.comp hp
  have hc2 := Nat.Primrec.left.comp (Nat.Primrec.right.comp hp)
  have hlt := primrec_isZero.comp
    (primrec_sub₂ (primrec_add₂ hi (Nat.Primrec.const 1)) hlen1)
  have hleft := primrec_nthCode.comp (hc1.pair (Nat.Primrec.pair hi (Nat.Primrec.const 0)))
  have hright := primrec_nthCode.comp
    (hc2.pair (Nat.Primrec.pair (primrec_sub₂ hi hlen1) (Nat.Primrec.const 0)))
  exact (primrec_selectFn hlt hleft hright).of_eq fun w => by
    unfold appendListTabFn
    simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
