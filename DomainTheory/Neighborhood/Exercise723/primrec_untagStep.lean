/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example78
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Theorem75
public import DomainTheory.Neighborhood.Exercise514
public import DomainTheory.Neighborhood.Exercise723.Basic
public import DomainTheory.Neighborhood.Exercise723.primrec_unnum1
public import DomainTheory.Neighborhood.Exercise723.primrec_unnum2

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)






























































theorem primrec_untagStep : Nat.Primrec untagStep := by
  have hdone : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hrevAcc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have ha : Nat.Primrec (fun w : ℕ => unnum1 w.unpair.1) := primrec_unnum1.comp Nat.Primrec.left
  have hb : Nat.Primrec (fun w : ℕ => unnum2 w.unpair.1) := primrec_unnum2.comp Nat.Primrec.left
  have hz : Nat.Primrec (fun w : ℕ => isZero (unnum1 w.unpair.1)) := primrec_isZero.comp ha
  have hhalt : Nat.Primrec (fun w : ℕ => Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1)))) :=
    hb.pair ((Nat.Primrec.const 1).pair (hrevAcc.pair hb))
  have hcont : Nat.Primrec (fun w : ℕ => Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 0
        (Nat.pair (Nat.pair (unnum1 w.unpair.1 - 1) w.unpair.2.unpair.2.unpair.1 + 1)
          w.unpair.2.unpair.2.unpair.2))) :=
    hb.pair ((Nat.Primrec.const 0).pair
      ((Nat.Primrec.succ.comp ((primrec_sub₂ ha (Nat.Primrec.const 1)).pair hrevAcc)).pair hval))
  have hinner := primrec_selectFn hz hhalt hcont
  exact (primrec_selectFn hdone primrec_id hinner).of_eq fun _ => rfl

end DomainTheory.Neighborhood.Exercise723
