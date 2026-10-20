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
import DomainTheory.Neighborhood.Exercise819.condSum_comp_sumToProdT
import DomainTheory.Neighborhood.Exercise819.sumToProdT_comp_condSum_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`E + E ⊴ T × (E × E)`.** -/
theorem sum_trianglelefteq_prodT : sum E E hE hE ⊴ prod TD (prod E E) :=
  trianglelefteq_of_projectionPair (sumToProdT hE) (condSum E E hE hE) (condSum_comp_sumToProdT hE)
    (sumToProdT_comp_condSum_le hE)

end Sum
end DomainTheory.Neighborhood
