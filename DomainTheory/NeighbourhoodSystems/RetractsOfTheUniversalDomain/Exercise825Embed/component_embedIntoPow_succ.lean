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


/-- Every coordinate past the head of `⟨x, ⊥, ⊥, …⟩` is `⊥`. -/
theorem component_embedIntoPow_succ (x : V.Element) (n : ℕ) :
    component ((embedIntoPow V).toElementMap x) (n + 1) = V.bot := by
  rw [toElementMap_embedIntoPow, ← component_tail, tail_push, Exercise618.component_bot]

end DomainTheory.Neighborhood
