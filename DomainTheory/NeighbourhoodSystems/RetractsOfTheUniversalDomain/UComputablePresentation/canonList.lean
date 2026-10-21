/-ai
Canonicalizing a list of rational pairs clips every pair into the half-open unit interval and discards degenerate pairs. If nothing survives, the result is the singleton list of the pair zero and one, which presents the master neighbourhood of U; otherwise it is the surviving list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Canonicalize** an arbitrary presenting list into one that presents a genuine
`U`-neighbourhood: clip every pair into `[0,1)` and discard degenerate pairs, falling back to the
single pair `(0,1)` (presenting `U.master`) if nothing survives. -/
def canonList (L : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  match (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with
  | [] => [((0 : ℚ), (1 : ℚ))]
  | L' => L'

end DomainTheory.NeighbourhoodSystems
