/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise316
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise511.Basic
public import DomainTheory.Neighborhood.Exercise511.fold_unfold

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)











/-- **Stack law.** `push(head z, tail z) = z` (a stack is its top pushed onto its tail). -/
theorem push_head_tail (z : (iterSys V).Element) :
    (push V).toElementMap (pair ((head V).toElementMap z) ((tail V).toElementMap z)) = z := by
  rw [head, tail, toElementMap_comp, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    pair_fst_snd, push, fold_unfold]

end DomainTheory.Neighborhood.Exercise511
