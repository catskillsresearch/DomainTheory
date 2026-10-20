/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition89
public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.Proposition810.Basic
public import DomainTheory.Neighborhood.Proposition810.prodComb_eq

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


theorem toElementMap_prodComb (a b : ApproximableMap U U) (x : U.Element) :
    (prodComb a b).toElementMap x =
      iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd)) := by
  rw [prodComb_eq]
  simp only [toElementMap_comp, toElementMap_prodMap]

end DomainTheory.Neighborhood
