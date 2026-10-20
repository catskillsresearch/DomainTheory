module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonFilterStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The code-level clip-and-filter pass, mirroring the list-level
`(L.map qpClip).filter (fun p => decide (p.1 < p.2))`. -/
def canonListCode (c : ℕ) : ℕ := flatMapCode (fun t => canonFilterStep t.unpair.2) 0 c

end DomainTheory.NeighbourhoodSystems
