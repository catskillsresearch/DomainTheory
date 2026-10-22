module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_myUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VunionRaw

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`VunionRaw` realizes `VX n ∪ VX m`** at the `levelSet` level (unconditionally). -/
theorem levelSet_VunionRaw (n m : ℕ) :
    levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2 = VX n ∪ VX m := by
  unfold VunionRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet_myUnion (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end DomainTheory.NeighbourhoodSystems
