module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}


/-- `fix`, as the element of `E = ((𝒟 → 𝒟) → 𝒟)` corresponding to the operator `fixMap`, unfolds
under `toApproxMap` back to `fixMap` (the `funSpace` round-trip). -/
theorem toApproxMap_toFilter_fixMap (V : NeighborhoodSystem α) :
    toApproxMap (toFilter (fixMap V)) = fixMap V := by
  have he := (funSpaceEquiv (funSpace V V) V).apply_symm_apply (fixMap V)
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he

end DomainTheory.NeighbourhoodSystems
