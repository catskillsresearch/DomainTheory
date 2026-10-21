/-ai
The canonical code of an index selects the stored code when the activity characteristic is on, and selects the Gödel code of sigma otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActiveChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- The Gödel code of `safeDecodeActive n` (`ssysCanonicalCode_eq`): `n`'s own decoded code if
active, else the code of `.sigma` (matching `safeDecodeActive`'s junk fallback). -/
@[irreducible] def ssysCanonicalCode (n : ℕ) : ℕ :=
  Domain.Recursive.selectFn (ssysActiveChar n) n.unpair.1 (SExpr.encode .sigma)

end Exercise722

end DomainTheory.NeighbourhoodSystems
