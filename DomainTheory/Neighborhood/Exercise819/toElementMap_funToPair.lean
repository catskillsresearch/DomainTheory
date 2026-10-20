/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise326Sum
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise819.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




theorem toElementMap_funToPair (φ : (funSpace TD E).Element) :
    (funToPair (E := E)).toElementMap φ
      = pair ((toApproxMap φ).toElementMap Example23.trueElt)
          ((toApproxMap φ).toElementMap Example23.falseElt) := by
  simp only [funToPair, toElementMap_paired, toElementMap_comp, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

end Prod
end DomainTheory.Neighborhood
