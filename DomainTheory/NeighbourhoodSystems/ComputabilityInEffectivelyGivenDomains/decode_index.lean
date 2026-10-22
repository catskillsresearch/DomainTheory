module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.index
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem SExpr.decode_index (e : SExpr) : decode (index e) = some e := by
  simp [decode, index]
  exact decodeFuel_encode (Nat.le_succ (sexprDepth e))

end Exercise722

end DomainTheory.NeighbourhoodSystems
