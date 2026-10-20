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
public import DomainTheory.Neighborhood.Exercise819.funToPair_comp_pairToFun
public import DomainTheory.Neighborhood.Exercise819.pairToFun_comp_funToPair_le

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **`E × E ⊴ (T → E)`.** -/
theorem prod_trianglelefteq_funSpace_TD : prod E E ⊴ funSpace TD E :=
  trianglelefteq_of_projectionPair pairToFun funToPair funToPair_comp_pairToFun
    pairToFun_comp_funToPair_le

end Prod
end DomainTheory.Neighborhood
