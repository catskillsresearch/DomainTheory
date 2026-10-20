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
public import DomainTheory.Neighborhood.Exercise820.evalBotMap_comp_constFunMap
public import DomainTheory.Neighborhood.Exercise820.constFunMap_comp_evalBotMap_le

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v




section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)




/-- **`B ⊴ funSpace A B`**, via `b ↦ (λ_. b)` / evaluation at `⊥`. -/
theorem trianglelefteq_funSpace_const : B ⊴ funSpace A B :=
  trianglelefteq_of_projectionPair (constFunMap A B) (evalBotMap A B)
    (evalBotMap_comp_constFunMap A B) (constFunMap_comp_evalBotMap_le A B)

end FunSpace
end DomainTheory.Neighborhood
