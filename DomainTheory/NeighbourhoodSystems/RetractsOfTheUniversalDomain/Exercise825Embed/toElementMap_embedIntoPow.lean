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

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


theorem toElementMap_embedIntoPow (x : V.Element) :
    (embedIntoPow V).toElementMap x = (push V).toElementMap (pair x (iterSys V).bot) := by
  rw [embedIntoPow, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

end DomainTheory.Neighborhood
