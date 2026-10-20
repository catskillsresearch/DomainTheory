/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem41.Basic
public import DomainTheory.Neighborhood.Theorem41.fixMap_toElementMap

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- `fix` applied to (the filter of) an approximable map `f` returns the least fixed point of `f`.
This is the bridge to the "for any `f : 𝒟 → 𝒟`" form of Theorem 4.2, using the Theorem 3.10
isomorphism `toApproxMap (toFilter f) = f`. -/
theorem fixMap_toElementMap_toFilter (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    (fixMap V).toElementMap (toFilter f) = f.fixElement := by
  rw [fixMap_toElementMap]
  have h : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv V V).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  rw [h]

end DomainTheory.Neighborhood
