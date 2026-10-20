/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.toElementMap_evalBotMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v




section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)




/-- `const_{φ(⊥)} ≤ φ` pointwise, since `φ(⊥) ≤ φ(x)` for every `x` (monotonicity,
`toElementMap_mono`, Proposition 2.2(iii), applied to `⊥ ≤ x`). -/
theorem constFunMap_comp_evalBotMap_le :
    (constFunMap A B).comp (evalBotMap A B) ≤ idMap (funSpace A B) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap]
  apply (funSpaceEquiv A B).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro a
  rw [toApproxMap_constFunMap, toElementMap_evalBotMap]
  exact toElementMap_mono (toApproxMap φ) (A.bot_le a)

end FunSpace
end DomainTheory.NeighbourhoodSystems
