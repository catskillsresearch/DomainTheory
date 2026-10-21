/-ai
The fixed-point map relates the enumerated neighbourhood of a code to the neighbourhood at an index if and only if some valid least-map chain from the master index ends inside that neighbourhood. This is Scott's characterization of the neighbourhood relation of fix by a finite sequence of steps.

The relation is membership of the enumerated neighbourhood in the principal filter. The fixed-point map sends that filter to the fixed-point element, and the chain characterization of membership applies at the master index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixElement_mem_iff_chain

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}






variable (P : ComputablePresentation V)

/-- **The `fix` neighbourhood relation, chain form.** `(fix V).rel (Xenum c) (X_ℓ)` holds iff there is
a valid least-map chain from the master index reaching a neighbourhood inside `X_ℓ`. This is Scott's
"`⋂[X_{nᵢ}, X_{mᵢ}] fix X_ℓ` iff for some finite sequence …". -/
theorem fixMap_rel_iff (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (c ℓ : ℕ) :
    (fixMap V).rel (Xenum P P gN c) (P.X ℓ) ↔
      ∃ full : List ℕ,
        gStepsOK (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))) P P.masterIdx full
        ∧ P.X (gLastOf P.masterIdx full) ⊆ P.X ℓ := by
  rw [(fixMap V).rel_iff_mem_principal (Xenum_mem P P gN hgN c), fixMap_toElementMap]
  exact fixElement_mem_iff_chain _ P P.masterIdx P.masterIdx_spec ℓ

end DomainTheory.NeighbourhoodSystems
