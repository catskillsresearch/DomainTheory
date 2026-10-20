/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Theorem76.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}






variable (P : ComputablePresentation V)





theorem primrec_fixStp (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fixStp fincl) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hprev : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hcode : Nat.Primrec (fun w : ℕ => codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hprev.pair hx).pair (Nat.Primrec.const 0))
  have hinner : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.2
      (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)) := hc.pair hcode
  have hsel : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0) :=
    primrec_selectFn hflag (primrec_isOne.comp (hfinclp.comp hinner)) (Nat.Primrec.const 0)
  exact (hx.pair hsel).of_eq (fun _ => rfl)

end DomainTheory.Neighborhood
