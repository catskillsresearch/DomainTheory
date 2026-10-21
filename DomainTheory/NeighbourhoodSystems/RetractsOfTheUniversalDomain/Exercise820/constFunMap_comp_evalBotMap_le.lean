/-ai
The composite of the constant-function embedding after evaluation at bottom lies below the identity on the function space from A to B.

Compare functions pointwise through the function-space equivalence. The constant function whose value is the given function at bottom, evaluated at an argument a, equals that value at bottom, which lies below the value at a by monotonicity, since bottom lies below a.
ai-/
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
