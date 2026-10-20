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
import DomainTheory.Neighborhood.Exercise819.prod_left_trianglelefteq
import DomainTheory.Neighborhood.Exercise819.prod_right_trianglelefteq
import DomainTheory.Neighborhood.Exercise819.prod_trianglelefteq_of
import DomainTheory.Neighborhood.Exercise819.sum_trianglelefteq_prodT


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **Exercise 8.19, Goal 2.** `T ⊴ E` and `E → E ⊴ E` give `E + E ⊴ E`: chain
`E+E ⊴ T×(E×E) ⊴ E×(E×E) ⊴ E×E ⊴ E`, using Goal 1 (applied twice, to peel off each product layer)
for the last two links. -/
theorem sum_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E := by
  have hPE : prod E E ⊴ E := prod_trianglelefteq_of hT hArrow
  exact trianglelefteq_trans
    (trianglelefteq_trans (sum_trianglelefteq_prodT hE) (prod_left_trianglelefteq (prod E E) hT))
    (trianglelefteq_trans (prod_right_trianglelefteq E hPE) hPE)

end Sum
end DomainTheory.Neighborhood
