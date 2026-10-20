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











































































































/-- **Bounded existential quantifier preserves recursive decidability.** Mirrors
`RecDecidable.bForall`, swapping `bForallFn` for `bExistsFn`. -/
theorem RecDecidable.bExists {p : ℕ → Prop} (hp : RecDecidable p) {bound : ℕ → ℕ}
    (hb : Nat.Primrec bound) :
    RecDecidable (fun n => ∃ i, i < bound n ∧ p (Nat.pair i n)) := by
  obtain ⟨f, hf, hfspec⟩ := hp
  refine ⟨fun n => bExistsFn f n (bound n), ?_, ?_⟩
  · have hGfn : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.2 1
        (isOne (f (Nat.pair w.unpair.2.unpair.1 w.unpair.1)))) :=
      primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 1)
        (primrec_isOne.comp (hf.comp
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
    have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
    refine (hprec.comp (primrec_id.pair hb)).of_eq (fun n => ?_)
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    rfl
  · intro n
    show (∃ i, i < bound n ∧ p (Nat.pair i n)) ↔ bExistsFn f n (bound n) = 1
    rw [bExistsFn_eq_one_iff]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, (hfspec _).mp h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, (hfspec _).mpr h⟩⟩

end Domain.Recursive
