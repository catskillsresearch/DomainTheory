module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_le_of_toElementMap_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2(ii) (Scott 1981, PRG-19).** `f(x) ⊆ x ⟹ fix(f) ⊆ x`: `fix` lands in the least
pre-fixed point. -/
theorem fixMap_least (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) {z : V.Element}
    (hz : (toApproxMap φ).toElementMap z ≤ z) : (fixMap V).toElementMap φ ≤ z := by
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap φ) hz

end DomainTheory.NeighbourhoodSystems
