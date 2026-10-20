/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Table55.Basic
import DomainTheory.Neighborhood.Table55.constC_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


















/-- `const(k)` is the constant map `constMap` of Lemma 3.6. -/
theorem constC_eq_constMap (k : V₁.Element) :
    toApproxMap ((constC V₀ V₁).toElementMap k) = constMap V₀ k := by
  apply ext_of_toElementMap
  intro x
  rw [constC_apply, toElementMap_constMap]

end DomainTheory.Neighborhood
