module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_inter_nonempty_iff_consistent
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_positivity

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem ssys_cons_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [ssys_cons_positivity, ssys_inter_nonempty_iff_consistent]

end Exercise722

end DomainTheory.NeighbourhoodSystems
