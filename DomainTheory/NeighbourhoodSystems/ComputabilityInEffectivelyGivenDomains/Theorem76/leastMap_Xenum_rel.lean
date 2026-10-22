module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)

/-- The least map `ĝ` of the function-space neighbourhood `Xenum c` relates `X_a` to `X_b` exactly
when `Xenum c ⊆ [X_a, X_b]` (Scott's `⋂{X_{mᵢ} ∣ X_a ⊆ X_{nᵢ}} ⊆ X_b`). -/
theorem leastMap_Xenum_rel (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (c a b : ℕ) :
    (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))).rel (P.X a) (P.X b)
      ↔ Xenum P P gN c ⊆ step (P.X a) (P.X b) := by
  rw [toApproxMap_rel, mem_principal]
  exact ⟨fun h => h.2, fun h => ⟨step_mem (P.mem_X a) (P.mem_X b), h⟩⟩

end DomainTheory.NeighbourhoodSystems
