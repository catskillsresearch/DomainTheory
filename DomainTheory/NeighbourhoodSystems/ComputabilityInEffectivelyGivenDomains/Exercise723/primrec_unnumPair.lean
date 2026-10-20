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
public import DomainTheory.Neighborhood.Exercise723.primrec_nextCellStep

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)























































theorem primrec_unnumPair : Nat.Primrec unnumPair := by
  have hbase : Nat.Primrec (fun _ : ℕ => Nat.pair (0 : ℕ) 0) := Nat.Primrec.const (Nat.pair 0 0)
  have hstep : Nat.Primrec (fun w : ℕ => nextCellStep w.unpair.2.unpair.2) :=
    primrec_nextCellStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine (hprec.comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq fun v => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  show Nat.rec (Nat.pair 0 0) (fun _ ih => nextCellStep ih) v = unnumPair v
  rw [rec_const_iterate]; rfl

end DomainTheory.Neighborhood.Exercise723
