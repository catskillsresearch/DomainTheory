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
public import DomainTheory.Neighborhood.Exercise511.unfold_fold

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)











/-- **Stack law.** `head(push(x, s)) = x`. -/
theorem head_push (x : V.Element) (s : (iterSys V).Element) :
    (head V).toElementMap ((push V).toElementMap (pair x s)) = x := by
  rw [head, toElementMap_comp, push, unfold_fold, toElementMap_proj₀, fst_pair]

end DomainTheory.Neighborhood.Exercise511
