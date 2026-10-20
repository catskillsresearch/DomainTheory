module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Ssys_cons_computable_of_primrec_ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.primrec_ssysConsChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- **Definition 7.1 (ii) is recursively decidable** (Exercise 7.22, closing C9). -/
theorem Ssys_cons_computable : RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  Ssys_cons_computable_of_primrec_ssysConsChar primrec_ssysConsChar

end Exercise722

end DomainTheory.NeighbourhoodSystems
