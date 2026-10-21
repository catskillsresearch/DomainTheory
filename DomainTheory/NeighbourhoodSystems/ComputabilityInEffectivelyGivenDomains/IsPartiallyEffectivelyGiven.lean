/-ai
A neighbourhood system is partially effectively given when it admits a consistency presentation, that is, when the consistency relation of an effective presentation is available.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- A neighbourhood system is *partially* effectively given when it admits a presentation
carrying relation (ii) (but not necessarily (i)). Named at top level (not `NeighborhoodSystem.…`)
since `Definition71.lean` — where `NeighborhoodSystem`/`ComputablePresentation` live — is outside
this session's edit scope; a future session may hoist `ConsistencyPresentation` there alongside
them for dot-notation parity with `IsEffectivelyGiven`. -/
def IsPartiallyEffectivelyGiven (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ConsistencyPresentation V)

end Exercise722

end DomainTheory.NeighbourhoodSystems
