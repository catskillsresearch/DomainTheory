/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise627.Basic
import DomainTheory.Neighborhood.Exercise627.strctMap_comp_inclMap
import DomainTheory.Neighborhood.Exercise627.inclMap_comp_strctMap_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

















section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










/-- **Exercise 6.27 (5).** `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` for all `𝒟, ℰ` (choice-free). -/
theorem strictFun_trianglelefteq_funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    strictFun V₀ V₁ ⊴ funSpace V₀ V₁ :=
  trianglelefteq_of_projectionPair inclMap strctMap strctMap_comp_inclMap inclMap_comp_strctMap_le

end Part5
end Exercise627
end DomainTheory.Neighborhood
