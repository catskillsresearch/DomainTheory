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

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)






















































theorem primrec_nextCellStep : Nat.Primrec nextCellStep := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun w : ℕ => w.unpair.2) := Nat.Primrec.right
  have hz : Nat.Primrec (fun w : ℕ => isZero w.unpair.1) := primrec_isZero.comp hn
  have ha : Nat.Primrec (fun w : ℕ => Nat.pair (w.unpair.2 + 1) 0) :=
    (primrec_add₂ hm (Nat.Primrec.const 1)).pair (Nat.Primrec.const 0)
  have hb : Nat.Primrec (fun w : ℕ => Nat.pair (w.unpair.1 - 1) (w.unpair.2 + 1)) :=
    (primrec_sub₂ hn (Nat.Primrec.const 1)).pair (primrec_add₂ hm (Nat.Primrec.const 1))
  exact (primrec_selectFn hz ha hb).of_eq fun _ => rfl

end DomainTheory.Neighborhood.Exercise723
