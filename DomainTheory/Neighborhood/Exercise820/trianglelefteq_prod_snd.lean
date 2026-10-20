/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise820.Basic
public import DomainTheory.Neighborhood.Exercise820.proju2081_comp_embedSnd
public import DomainTheory.Neighborhood.Exercise820.embedSnd_comp_proju2081_le

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v


section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)



/-- **`B ⊴ prod A B`**, via `b ↦ ⟨⊥, b⟩` / `proj₁`. -/
theorem trianglelefteq_prod_snd : B ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedSnd A B) (proj₁ A B) (proj₁_comp_embedSnd A B)
    (embedSnd_comp_proj₁_le A B)

end Prod
end DomainTheory.Neighborhood
