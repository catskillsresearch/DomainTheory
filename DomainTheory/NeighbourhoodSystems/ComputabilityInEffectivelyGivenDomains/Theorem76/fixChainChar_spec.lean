/-ai
The first component of the chain characteristic is the last index of the decoded list starting from the master index, and its second component equals 1 if and only if the decidable chain predicate holds of that list from the master index.

Rewrite the characteristic as the left fold of the pure step. The first-component lemma reads off the last index, and the second-component lemma, applied to the start flag 1, reads off the chain predicate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixChainChar_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixPStep_foldl_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixPStep_foldl_snd

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}






variable (P : ComputablePresentation V)






/-- Read-off of the `foldCode`: its `.1` is the last index of `decodeList i`, and its `.2 = 1` iff
the decoded chain is consistent. -/
theorem fixChainChar_spec (fincl : ℕ → ℕ) (c i : ℕ) :
    (fixChainChar P fincl c i).unpair.1 = gLastOf P.masterIdx (decodeList i)
  ∧ ((fixChainChar P fincl c i).unpair.2 = 1 ↔ chainDec fincl c P.masterIdx (decodeList i)) := by
  rw [fixChainChar_eq]
  refine ⟨fixPStep_foldl_fst fincl c (decodeList i) P.masterIdx 1, ?_⟩
  rw [fixPStep_foldl_snd fincl c (decodeList i) P.masterIdx 1 (le_refl 1)]
  simp

end DomainTheory.NeighbourhoodSystems
