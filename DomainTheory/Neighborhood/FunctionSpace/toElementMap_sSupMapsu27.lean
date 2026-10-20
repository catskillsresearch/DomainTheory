/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic
import DomainTheory.Neighborhood.FunctionSpace.mapsBounded_iff_pointwiseBounded
import DomainTheory.Neighborhood.FunctionSpace.toElementMap_sSupMaps


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
















































/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** When `F` is bounded, `(⊔F)(x) = ⊔{f(x) ∣ f ∈ F}`
(stated with the boundedness hypothesis in Scott's `MapsBounded` form). -/
theorem toElementMap_sSupMaps' {F : Set (ApproximableMap V₀ V₁)} (hF : MapsBounded F) (x : V₀.Element) :
    (sSupMaps F (mapsBounded_iff_pointwiseBounded.mp hF)).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F)
        (mapsBounded_iff_pointwiseBounded.mp hF x) :=
  toElementMap_sSupMaps (mapsBounded_iff_pointwiseBounded.mp hF) x

end DomainTheory.Neighborhood
