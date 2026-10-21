/-ai
An approximable operator from the function space that fixes each argument on its own value, and that lies below every pre-fixed point, equals the fixed-point operator.

Extensionality of maps that induce the same elementwise function reduces the claim to each element. The two values lie below one another: the rival lies below the fixed-point value because that value is a fixed point, and the fixed-point value lies below the rival because the rival value is a pre-fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_fixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_least

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2 (Scott 1981, PRG-19) — uniqueness.** Any approximable operator `fax` satisfying
(i) and (ii) coincides with `fix`. (Scott: from (i)(ii) one proves `fix(f) ⊆ fax(f)` and
`fax(f) ⊆ fix(f)`.) -/
theorem fixMap_unique (V : NeighborhoodSystem α) (fax : ApproximableMap (funSpace V V) V)
    (h_fix : ∀ φ, (toApproxMap φ).toElementMap (fax.toElementMap φ) = fax.toElementMap φ)
    (h_least : ∀ (φ : (funSpace V V).Element) (z : V.Element),
      (toApproxMap φ).toElementMap z ≤ z → fax.toElementMap φ ≤ z) :
    fax = fixMap V := by
  apply ext_of_toElementMap
  intro φ
  apply le_antisymm
  · exact h_least φ _ (le_of_eq (fixMap_fixed V φ))
  · exact fixMap_least V φ (le_of_eq (h_fix φ))

end DomainTheory.NeighbourhoodSystems
