module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

set_option linter.unusedSectionVars false

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
