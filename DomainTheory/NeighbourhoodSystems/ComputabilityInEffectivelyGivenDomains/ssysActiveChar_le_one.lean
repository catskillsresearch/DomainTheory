/-ai
The activity characteristic of any coded index is at most 1.

It is a bit product, and the bounds on the fuel-bounded decode characteristic and on the bounded-existence characteristic make the product at most 1.
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

theorem ssysActiveChar_le_one (n : ℕ) : ssysActiveChar n ≤ 1 :=
  mulBit_le_one (decodeFuelOkChar_le_one _ _) (bExistsFn_le_one _ _ _)

end Exercise722

end DomainTheory.NeighbourhoodSystems
