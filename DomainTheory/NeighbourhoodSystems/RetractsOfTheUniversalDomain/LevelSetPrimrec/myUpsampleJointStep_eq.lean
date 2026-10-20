module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Unfolding equation for `myUpsampleJointStep`, stated so `rw` fires on a single (outer)
occurrence rather than `unfold`ing every nested occurrence (in particular, the ones hidden inside
an already-iterated `myUpsampleJointStep^[d]` term). -/
theorem myUpsampleJointStep_eq (s : ℕ) :
    myUpsampleJointStep s = Nat.pair (s.unpair.1 + 1) (myUpsampleStep s.unpair.1 s.unpair.2) := rfl

end DomainTheory.NeighbourhoodSystems
