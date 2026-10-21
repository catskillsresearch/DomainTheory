/-ai
The consistency characteristic of a paired index is the boolean-to-natural encoding of the consistency decision on its two unpaired components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- `{0,1}` packaging of `ssysConsistentB` on `Nat.pair`-coded index pairs. -/
def ssysConsChar (t : ℕ) : ℕ := boolNat (ssysConsistentB t.unpair.1 t.unpair.2)

end Exercise722

end DomainTheory.NeighbourhoodSystems
