/-ai
The intersection of two level sets is the level set, at the maximum of the two levels,
of the bitwise conjunction of the two masks upsampled to that level.

Each factor is rewritten by preservation of the level set under upsampling to the
corresponding side of the maximum. The same-level intersection formula and the
correctness of the iterative bitwise conjunction give the result.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLand
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLand_eq_land
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myUpsample

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_inter_same_level
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Computable version of `levelSet_inter`.** -/
theorem levelSet_myInter (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∩ levelSet k2 m2
      = levelSet (max k1 k2) (myLand (myUpsample k1 (max k1 k2) m1) (myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet_myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet_inter_same_level, myLand_eq_land]

end DomainTheory.NeighbourhoodSystems
