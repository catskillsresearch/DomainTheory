module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_fixed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `fix(f) = f(fix(f))`. -/
theorem fixC_fixed (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixC V).toElementMap φ) = (fixC V).toElementMap φ := by
  rw [fixC]; exact fixMap_fixed V φ

end DomainTheory.NeighbourhoodSystems
