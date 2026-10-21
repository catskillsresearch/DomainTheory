/-ai
If the neighbourhood at a start index is the master neighbourhood, then the fixed-point element of a map contains the neighbourhood at an index if and only if some valid chain from that start index ends at a neighbourhood contained in the neighbourhood at the index.

Membership in the fixed-point element is an iterate relation from the master neighbourhood. Completeness turns such an iterate into a chain after rewriting the start neighbourhood as the master. Conversely, soundness realises the chain as an iterate of the same length, and monotonicity along the final inclusion, rewritten back through the master neighbourhood, gives membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.gStepsOK_sound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.gStepsOK_complete

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}




/-- **Chain characterisation of `g`'s least fixed point.** A neighbourhood `X_ℓ` is in `fix(g)` iff a
valid `g`-chain (from a master index `a₀` with `X_{a₀} = Δ`) reaches a final neighbourhood inside
`X_ℓ`. -/
theorem fixElement_mem_iff_chain (g : ApproximableMap V V) (P : ComputablePresentation V)
    (a0 : ℕ) (ha0 : P.X a0 = V.master) (ℓ : ℕ) :
    g.fixElement.mem (P.X ℓ) ↔
      ∃ full, gStepsOK g P a0 full ∧ P.X (gLastOf a0 full) ⊆ P.X ℓ := by
  rw [mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩
    rw [← ha0] at hn
    exact gStepsOK_complete g P n a0 ℓ hn
  · rintro ⟨full, hsteps, hlast⟩
    refine ⟨full.length, ?_⟩
    have hsound := gStepsOK_sound g P full a0 hsteps
    have hmono := (g.iterMap full.length).mono hsound subset_rfl hlast (P.mem_X a0) (P.mem_X ℓ)
    rwa [ha0] at hmono

end DomainTheory.NeighbourhoodSystems
