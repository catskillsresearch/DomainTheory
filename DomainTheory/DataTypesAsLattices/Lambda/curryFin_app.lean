/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.curryFin_isScottContinuous


namespace DomainTheory.DataTypesAsLattices



















theorem curryFin_app {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) (xs : Fin n → Pomega) :
    nestApplyFin (curryFin f) xs = f xs := by
  induction n with
  | zero =>
    change curryFin f = f xs
    exact congrArg f (funext fun i => nomatch i)
  | succ n ih =>
    have hβ : funOf (curryFin f) (xs 0) =
        curryFin (fun ys => f (Fin.cons (xs 0) ys)) :=
      beta (curryFin_isScottContinuous hf) (xs 0)
    change nestApplyFin (funOf (curryFin f) (xs 0)) (Fin.tail xs) = f xs
    rw [hβ, ih (hf.2 (xs 0)) (Fin.tail xs)]
    exact congrArg f (Fin.cons_self_tail xs)

end DomainTheory.DataTypesAsLattices
