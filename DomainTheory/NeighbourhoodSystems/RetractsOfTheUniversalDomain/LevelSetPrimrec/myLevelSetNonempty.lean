/-ai
The nonemptiness test of a level and a mask is the value in {0, 1} deciding whether the
corresponding level set is nonempty. It is the bounded existential, up to two to the
power of the level, of the bit test of the mask.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSetNonemptyBody

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`myLevelSetNonempty k m ∈ {0,1}`** decides `(levelSet k m).Nonempty`
(`myLevelSetNonempty_eq_one_iff`). -/
def myLevelSetNonempty (k m : ℕ) : ℕ := bExistsFn levelSetNonemptyBody m (2 ^ k)

end DomainTheory.NeighbourhoodSystems
