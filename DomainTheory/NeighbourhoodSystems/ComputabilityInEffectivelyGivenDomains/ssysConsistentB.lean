module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- `{0,1}` consistency decider on index pairs (active-active uses `consistentB`). -/
def ssysConsistentB (n m : ℕ) : Bool :=
  if !ssysActive n || !ssysActive m then true
  else
    match SExpr.decode n, SExpr.decode m with
    | some a, some b => consistentB a b
    | _, _ => true

end Exercise722

end DomainTheory.NeighbourhoodSystems
