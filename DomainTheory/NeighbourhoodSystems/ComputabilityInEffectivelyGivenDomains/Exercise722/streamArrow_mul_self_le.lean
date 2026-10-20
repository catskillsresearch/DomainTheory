module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.prependMap_iterElem_mul_streamArrow_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`σ⃗·σ⃗ ≤ σ⃗`**: `σ⃗`'s membership witnesses come from *some* finite approximant `fⁿ(⊥)`
(`mem_fixElement`/`mem_iterElem`), and every approximant satisfies the per-`n` bound above. -/
theorem streamArrow_mul_self_le (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) ≤ streamArrow σ := by
  rintro Z ⟨hInSZ, X, hX, Y, hY, hsub⟩
  obtain ⟨n, hn⟩ := (mem_fixElement (prependMap σ)).mp hX
  have hXn : ((prependMap σ).iterElem n).mem X := (mem_iterElem (prependMap σ) n).mpr hn
  exact prependMap_iterElem_mul_streamArrow_le σ n Z ⟨hInSZ, X, hXn, Y, hY, hsub⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
