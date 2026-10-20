module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sexprDepth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem c9b5_sexprDepth_eq (e : SExpr) : Domain.Recursive.c9b5_sexprDepth e = sexprDepth e := by
  induction e with
  | sigma => rfl
  | single _ => rfl
  | cat a b iha ihb => simp [Domain.Recursive.c9b5_sexprDepth, sexprDepth, iha, ihb]
  | cap a b iha ihb => simp [Domain.Recursive.c9b5_sexprDepth, sexprDepth, iha, ihb]

end Exercise722

end DomainTheory.NeighbourhoodSystems
