module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.gLastOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.gStepsOK
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.codePair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.chainDec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixPStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixChainChar

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


/-- **Completeness of a chain.** If `(gⁿ).rel (X_a) (X_ℓ)`, then there is a valid `g`-chain from `a`
whose final neighbourhood is contained in `X_ℓ`. (The intermediate neighbourhoods are named via
`surj`; the relaxed final condition `X_{last} ⊆ X_ℓ` handles the `n = 0` base.) -/
theorem gStepsOK_complete (g : ApproximableMap V V) (P : ComputablePresentation V) :
    ∀ (n a ℓ : ℕ), (g.iterMap n).rel (P.X a) (P.X ℓ) →
      ∃ full, gStepsOK g P a full ∧ P.X (gLastOf a full) ⊆ P.X ℓ := by
  intro n
  induction n with
  | zero =>
    intro a ℓ h
    rw [iterMap_zero, idMap_rel] at h
    exact ⟨[], trivial, h.2.2⟩
  | succ n ih =>
    intro a ℓ h
    have hcomm : g.iterMap (n + 1) = (g.iterMap n).comp g := by
      rw [iterMap_succ]; exact iter_comm g n
    rw [hcomm, comp_rel] at h
    obtain ⟨Y, h1, h2⟩ := h
    obtain ⟨k, hk⟩ := P.surj (g.rel_cod h1)
    rw [← hk] at h1 h2
    obtain ⟨full', hs', hl'⟩ := ih k ℓ h2
    exact ⟨k :: full', ⟨h1, hs'⟩, hl'⟩

end DomainTheory.NeighbourhoodSystems
