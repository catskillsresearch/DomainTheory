module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Decoder: `Nat.unpair n` supplies `(code, fuel)` with `fuel = sexprDepth e` on valid indices. -/
def SExpr.decode (n : ℕ) : Option SExpr := decodeFuel (n.unpair.2 + 1) n.unpair.1

end Exercise722

end DomainTheory.NeighbourhoodSystems
