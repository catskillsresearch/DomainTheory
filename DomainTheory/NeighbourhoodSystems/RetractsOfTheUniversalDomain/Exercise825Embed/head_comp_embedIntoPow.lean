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
public import DomainTheory.Neighborhood.Exercise825Embed.component_embedIntoPow_zero

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **`head` retracts `embedIntoPow`.** -/
theorem head_comp_embedIntoPow : (head V).comp (embedIntoPow V) = idMap V :=
  ApproximableMap.ext_of_toElementMap fun x => by
    rw [toElementMap_comp, toElementMap_idMap, head_apply, component_embedIntoPow_zero]

end DomainTheory.Neighborhood
