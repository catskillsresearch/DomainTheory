module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_eq_denote_safe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem ssys_inter_nonempty_iff_consistent (n m : ℕ) :
    (SsysX n ∩ SsysX m).Nonempty ↔ consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, ← denote_cap, consistentB_iff]

end Exercise722

end DomainTheory.NeighbourhoodSystems
