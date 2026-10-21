/-ai
The approximable map corresponding to a function-space element fixes the value of the fixed-point operator at that element.

The elementwise equation rewrites the operator value as the least fixed point of that map, and the least fixed point is a fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2(i) (Scott 1981, PRG-19).** `fix(f) = f(fix(f))`: the value of `fix` is a fixed
point of the argument. (Equivalently `eval(f, fix(f)) = fix(f)` by `evalMap_apply`.) -/
theorem fixMap_fixed (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixMap V).toElementMap φ) = (fixMap V).toElementMap φ := by
  rw [fixMap_toElementMap]
  exact toElementMap_fixElement (toApproxMap φ)

end DomainTheory.NeighbourhoodSystems
