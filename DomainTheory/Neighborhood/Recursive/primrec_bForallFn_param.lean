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











































































































/-- Parametrized variant of `bForallFn`'s joint primrec (mirrors `primrec_bExistsFn_param`,
swapping `selectFn`'s branches to match `bForallFn`'s `1`-base / AND-style step). -/
theorem primrec_bForallFn_param {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bForallFn (fun p => g (Nat.pair t.unpair.1.unpair.1 p))
      t.unpair.1.unpair.2 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2
        (isOne (g (Nat.pair w.unpair.1.unpair.1
          (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)))) 0) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (primrec_isOne.comp (hg.comp
        (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
          (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
            (Nat.Primrec.right.comp Nat.Primrec.left)))))
      (Nat.Primrec.const 0)
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 1) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

end Domain.Recursive
