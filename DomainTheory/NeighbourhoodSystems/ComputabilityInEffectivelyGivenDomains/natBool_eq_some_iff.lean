/-ai
A natural number interprets as a given boolean if and only if the number equals the boolean-to-natural encoding of that boolean.

Match the number against 0, 1, and every larger value, and match the boolean. The values 0 and 1 agree with the two encodings, and every larger value fails on both sides.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem natBool_eq_some_iff (n : ℕ) (b : Bool) : natBool n = some b ↔ n = boolNat b := by
  match n with
  | 0 => cases b <;> simp [natBool, boolNat]
  | 1 => cases b <;> simp [natBool, boolNat]
  | n + 2 => cases b <;> simp [natBool, boolNat]

end Exercise722

end DomainTheory.NeighbourhoodSystems
