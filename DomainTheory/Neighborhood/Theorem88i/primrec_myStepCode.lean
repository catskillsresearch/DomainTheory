/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88h
import DomainTheory.Neighborhood.Theorem88i.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)





variable {P qChar cons}

variable (P qChar cons)




theorem primrec_myStepCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myStepCode P qChar cons) := by
  have he : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) := Nat.Primrec.right.comp he
  have hargs : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    hr.pair he2
  have hqchar_e : Nat.Primrec (fun w : ℕ => qChar w.unpair.1) := hqCharp.comp he
  have hcons_val : Nat.Primrec
      (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)) :=
    hconsp.comp hargs
  have hcond : Nat.Primrec (fun w : ℕ =>
      isOne (qChar w.unpair.1) * isOne (cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))) :=
    primrec_mul₂ (primrec_isOne.comp hqchar_e) (primrec_isOne.comp hcons_val)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    (P.inter_primrec.comp hargs).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hinter hr).of_eq fun _ => rfl

end DomainTheory.Neighborhood
