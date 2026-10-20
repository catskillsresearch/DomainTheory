module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem ssys_cons_char_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔ ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m := by
  rw [ssysConsistentB_iff, ssys_cons_iff]

end Exercise722

end DomainTheory.NeighbourhoodSystems
