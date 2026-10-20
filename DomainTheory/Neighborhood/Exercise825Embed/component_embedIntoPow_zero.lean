/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise511
public import DomainTheory.Neighborhood.Exercise618
public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Exercise825Embed.Basic
public import DomainTheory.Neighborhood.Exercise825Embed.toElementMap_embedIntoPow

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The head of the singleton stack `⟨x, ⊥, ⊥, …⟩` is `x`. -/
theorem component_embedIntoPow_zero (x : V.Element) :
    component ((embedIntoPow V).toElementMap x) 0 = x := by
  rw [toElementMap_embedIntoPow, ← head_apply, head_push]

end DomainTheory.Neighborhood
