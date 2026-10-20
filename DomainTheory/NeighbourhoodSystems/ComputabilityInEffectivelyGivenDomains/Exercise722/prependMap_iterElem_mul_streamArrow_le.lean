module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.prependMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mulElem_mono_right
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mulElem_bot_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **Per-approximant bound**: `fⁿ(⊥) · σ⃗ ≤ σ⃗`, by induction using `mulElem_bot_le` (base case)
and associativity + monotonicity + `streamArrow_eq` (step). -/
theorem prependMap_iterElem_mul_streamArrow_le (σ : List Bool) :
    ∀ n, mulElem ((prependMap σ).iterElem n) (streamArrow σ) ≤ streamArrow σ
  | 0 => by
      have h0 : (prependMap σ).iterElem 0 = Ssys.bot := by
        show (idMap Ssys).toElementMap Ssys.bot = Ssys.bot
        exact toElementMap_idMap Ssys.bot
      rw [h0]
      exact mulElem_bot_le (streamArrow σ)
  | n + 1 => by
      have hsucc : (prependMap σ).iterElem (n + 1) =
          mulElem (emb σ) ((prependMap σ).iterElem n) := by
        show ((prependMap σ).comp ((prependMap σ).iterMap n)).toElementMap Ssys.bot = _
        rw [toElementMap_comp]
        exact prependMap_toElementMap σ _
      rw [hsucc, mulElem_assoc]
      calc mulElem (emb σ) (mulElem ((prependMap σ).iterElem n) (streamArrow σ))
          ≤ mulElem (emb σ) (streamArrow σ) :=
            mulElem_mono_right (emb σ) (prependMap_iterElem_mul_streamArrow_le σ n)
        _ = streamArrow σ := streamArrow_eq σ

end Exercise722
end DomainTheory.NeighbourhoodSystems
