module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_char_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_eq_one_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem ssys_cons_char_eq_one_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ ssysConsChar (Nat.pair n m) = 1 := by
  rw [ssysConsChar_eq_one_iff, ssys_cons_char_iff, unpair_pair_fst, unpair_pair_snd]

end Exercise722

end DomainTheory.NeighbourhoodSystems
