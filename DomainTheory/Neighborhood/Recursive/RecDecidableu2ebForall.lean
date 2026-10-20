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











































































































/-- **Bounded universal quantifier preserves recursive decidability.** If `p` is recursively decidable
and `bound` is primitive recursive, then `fun n => ∀ i < bound n, p (pair i n)` is recursively
decidable (choice-free). -/
theorem RecDecidable.bForall {p : ℕ → Prop} (hp : RecDecidable p) {bound : ℕ → ℕ}
    (hb : Nat.Primrec bound) :
    RecDecidable (fun n => ∀ i, i < bound n → p (Nat.pair i n)) := by
  obtain ⟨f, hf, hfspec⟩ := hp
  refine ⟨fun n => bForallFn f n (bound n), ?_, ?_⟩
  · have hGfn : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.2
        (isOne (f (Nat.pair w.unpair.2.unpair.1 w.unpair.1))) 0) :=
      primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
        (primrec_isOne.comp (hf.comp
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
        (Nat.Primrec.const 0)
    have hprec := Nat.Primrec.prec (Nat.Primrec.const 1) hGfn
    refine (hprec.comp (primrec_id.pair hb)).of_eq (fun n => ?_)
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    rfl
  · intro n
    show (∀ i, i < bound n → p (Nat.pair i n)) ↔ bForallFn f n (bound n) = 1
    rw [bForallFn_eq_one_iff]
    exact ⟨fun h i hi => (hfspec _).mp (h i hi), fun h i hi => (hfspec _).mpr (h i hi)⟩

end Domain.Recursive
