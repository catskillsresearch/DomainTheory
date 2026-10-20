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
public import DomainTheory.Neighborhood.Exercise723.untagStep_iter_spec

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)































































theorem untagState_spec (c : ℕ) :
    untagState c = Nat.pair (untagRef c).2
      (Nat.pair 1 (Nat.pair ((untagRef c).1.foldl (fun acc x => Nat.pair x acc + 1) 0)
        (untagRef c).2)) :=
  untagStep_iter_spec c c 0 0 (le_refl c)

end DomainTheory.Neighborhood.Exercise723
