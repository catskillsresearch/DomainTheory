/-ai
The consistency decision on two indices is true if and only if the safe active decodes of those indices are consistent.

If both indices are active, both decodes succeed and are nonempty, so the safe decodes are those expressions, and unfolding the decision shows that it equals their consistency. If the second index is inactive, its safe decode is sigma, which is consistent with the safe decode of the first, and the decision is true. If the first index is inactive, its safe decode is sigma, which is consistent with the safe decode of the second, and the decision is true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive_inactive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.consistentB_sigma_safe
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.consistentB_safe_sigma

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem ssysConsistentB_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  by_cases hn : ssysActive n
  · by_cases hm : ssysActive m
    · cases hdecn : SExpr.decode n with
      | none => exfalso; simp [ssysActive, hdecn] at hn
      | some a =>
        cases hdecm : SExpr.decode m with
        | none => exfalso; simp [ssysActive, hdecm] at hm
        | some b =>
          have ha : decideNonemptyB a := by simpa [ssysActive, hdecn] using hn
          have hb : decideNonemptyB b := by simpa [ssysActive, hdecm] using hm
          have hsa : safeDecodeActive n = a := by simp [safeDecodeActive, hdecn, ha]
          have hsb : safeDecodeActive m = b := by simp [safeDecodeActive, hdecm, hb]
          constructor
          · intro h
            rw [hsa, hsb]
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
            rw [heq] at h
            exact h
          · intro hcons
            rw [hsa, hsb] at hcons
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
            rw [heq]
            exact hcons
    · have hm' : ssysActive m = false := by simpa using hm
      constructor
      · intro _; rw [safeDecodeActive_inactive m hm', consistentB_safe_sigma n]
      · intro _; unfold ssysConsistentB; simp [hn, hm']
  · have hn' : ssysActive n = false := by simpa using hn
    constructor
    · intro _; rw [safeDecodeActive_inactive n hn', consistentB_sigma_safe m]
    · intro _; unfold ssysConsistentB; simp [hn']

end Exercise722

end DomainTheory.NeighbourhoodSystems
