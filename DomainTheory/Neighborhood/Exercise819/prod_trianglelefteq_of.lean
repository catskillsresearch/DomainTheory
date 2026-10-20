/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Exercise326Sum
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise819.Basic
import DomainTheory.Neighborhood.Exercise819.funSpace_dom_trianglelefteq
import DomainTheory.Neighborhood.Exercise819.prod_trianglelefteq_funSpace_TD


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **Exercise 8.19, Goal 1.** `T ⊴ E` and `E → E ⊴ E` give `E × E ⊴ E`: chain `E×E ⊴ (T→E) ⊴
(E→E) ⊴ E`. -/
theorem prod_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    prod E E ⊴ E :=
  trianglelefteq_trans
    (trianglelefteq_trans prod_trianglelefteq_funSpace_TD (funSpace_dom_trianglelefteq E hT))
    hArrow

end Prod
end DomainTheory.Neighborhood
