/-ai
The index of an expression is the pairing of its Gödel code with its depth.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Index for the enumeration: code plus depth (fuel for decoding). -/
def SExpr.index (e : SExpr) : ℕ := Nat.pair (encode e) (sexprDepth e)

end Exercise722

end DomainTheory.NeighbourhoodSystems
