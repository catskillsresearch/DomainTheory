/-ai
Decoding the index of an expression recovers the expression.

Unfold decoding and the index. The index pairs the Gödel code with the depth, and fuel-bounded decoding inverts encoding at fuel one more than the depth.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.index
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem SExpr.decode_index (e : SExpr) : decode (index e) = some e := by
  simp [decode, index]
  exact decodeFuel_encode (Nat.le_succ (sexprDepth e))

end Exercise722

end DomainTheory.NeighbourhoodSystems
