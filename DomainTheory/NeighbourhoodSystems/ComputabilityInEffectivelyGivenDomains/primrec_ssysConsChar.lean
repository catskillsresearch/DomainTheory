module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.primrec_ssysConsistentBChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_eq_ssysConsistentBChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- **7.22i(b)8 / closes the C9b umbrella.** -/
theorem primrec_ssysConsChar : Nat.Primrec ssysConsChar :=
  (primrec_ssysConsistentBChar).of_eq fun t => (ssysConsChar_eq_ssysConsistentBChar t).symm

end Exercise722

end DomainTheory.NeighbourhoodSystems
