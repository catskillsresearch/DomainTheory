/-ai
The consistency characteristic of any two coded indices is at most 1.

The product of the two activity characteristics is 0 or 1, since each characteristic is at most 1. The selector then returns either 1 or the code consistency characteristic, which is at most 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar_le_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentBChar

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem ssysConsistentBChar_le_one (n m : ℕ) : ssysConsistentBChar n m ≤ 1 := by
  unfold ssysConsistentBChar
  rcases (show mulBit (ssysActiveChar n) (ssysActiveChar m) = 0 ∨
      mulBit (ssysActiveChar n) (ssysActiveChar m) = 1 by
    have h1 := ssysActiveChar_le_one n
    have h2 := ssysActiveChar_le_one m
    unfold mulBit
    rcases (show ssysActiveChar n = 0 ∨ ssysActiveChar n = 1 by omega) with hn | hn <;>
      rcases (show ssysActiveChar m = 0 ∨ ssysActiveChar m = 1 by omega) with hm | hm <;>
      simp [hn, hm]) with h0 | h1
  · rw [h0, selectFn_zero]
  · rw [h1, selectFn_one]; exact consistentBChar_le_one _ _ _

end Exercise722

end DomainTheory.NeighbourhoodSystems
