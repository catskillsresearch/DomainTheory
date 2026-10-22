module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- `{0,1}` packaging of `ssysActive` via `decodeFuelOkChar` (C9b1) + `decideNonemptyBChar`
(C9b6), operating purely on the Gödel code `n.unpair.1` with fuel `n.unpair.2 + 1` (mirroring
`SExpr.decode`). -/
def ssysActiveChar (n : ℕ) : ℕ :=
  mulBit (decodeFuelOkChar (n.unpair.2 + 1) n.unpair.1)
    (decideNonemptyBChar (n.unpair.2 + 1) n.unpair.1)

end Exercise722

end DomainTheory.NeighbourhoodSystems
