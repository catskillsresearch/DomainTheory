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
public import DomainTheory.Neighborhood.Exercise723.primrec_untagState

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

































































theorem primrec_untagList : Nat.Primrec untagList :=
  primrec_appendCode.comp
    ((Nat.Primrec.const 0).pair
      (Nat.Primrec.left.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp primrec_untagState))))
    |>.of_eq fun c => by unfold untagList; simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood.Exercise723
