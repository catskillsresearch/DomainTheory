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
public import DomainTheory.Neighborhood.Exercise511.mapBody_apply

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


















/-- **Exercise 5.11 (Scott 1981, PRG-19).** The recursion defining `map`:
`map(s, x) = push((head s)(x), map(tail s, x))`. -/
theorem map_rec (s : (iterSys (funSpace V V)).Element) (x : V.Element) :
    (mapMap V).toElementMap (pair s x) =
      (push V).toElementMap
        (pair ((toApproxMap ((head (funSpace V V)).toElementMap s)).toElementMap x)
          ((mapMap V).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x))) := by
  have hfix : (mapOp V).toElementMap (mapOp V).fixElement = (mapOp V).fixElement :=
    toElementMap_fixElement (mapOp V)
  have hval := toElementMap_curry_apply (mapBody V) (mapOp V).fixElement (pair s x)
  rw [← mapOp, hfix] at hval
  rw [mapMap, hval, mapBody_apply]

end DomainTheory.Neighborhood.Exercise511
