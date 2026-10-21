/-ai
The consistency characteristic of two coded indices selects the consistency characteristic of their stored codes, at fuel the sum of the two stored depths plus two, when both activity characteristics are on, and selects 1 otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- `{0,1}` packaging of `ssysConsistentB`: inactive-either defaults to `1` (consistent), while
active-active reduces to `consistentBChar` (C9b6). Fuel `n.unpair.2 + m.unpair.2 + 2` is generous
enough for the `.cap` of both decoded expressions regardless of which side is deeper. -/
def ssysConsistentBChar (n m : ℕ) : ℕ :=
  selectFn (mulBit (ssysActiveChar n) (ssysActiveChar m))
    (consistentBChar (n.unpair.2 + m.unpair.2 + 2) n.unpair.1 m.unpair.1)
    1

end Exercise722

end DomainTheory.NeighbourhoodSystems
