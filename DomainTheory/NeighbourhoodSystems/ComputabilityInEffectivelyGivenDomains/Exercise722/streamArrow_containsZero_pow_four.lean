module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_mul_self

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap


/-- **Scott's fourth equation (the concrete numeric instance).** `01⃗·01⃗·01⃗·01⃗ = 01⃗·01⃗`, for
`01⃗ := streamArrow [false, true]`. Follows from `streamArrow_mul_self` applied twice. -/
theorem streamArrow_containsZero_pow_four :
    mulElem
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
      = mulElem (streamArrow [false, true]) (streamArrow [false, true]) := by
  rw [streamArrow_mul_self, streamArrow_mul_self]

end Exercise722
end DomainTheory.NeighbourhoodSystems
