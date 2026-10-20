/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise820.Basic
import DomainTheory.Neighborhood.Exercise820.proju2080_comp_embedFst
import DomainTheory.Neighborhood.Exercise820.embedFst_comp_proju2080_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v


section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)



/-- **`A ⊴ prod A B`**, via `a ↦ ⟨a, ⊥⟩` / `proj₀`. -/
theorem trianglelefteq_prod_fst : A ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedFst A B) (proj₀ A B) (proj₀_comp_embedFst A B)
    (embedFst_comp_proj₀_le A B)

end Prod
end DomainTheory.Neighborhood
