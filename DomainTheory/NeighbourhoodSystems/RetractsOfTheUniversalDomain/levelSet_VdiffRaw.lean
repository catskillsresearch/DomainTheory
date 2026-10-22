module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_myDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`VdiffRaw` realizes `VX n \ VX m`** at the `levelSet` level (unconditionally). -/
theorem levelSet_VdiffRaw (n m : ℕ) :
    levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2 = VX n \ VX m := by
  unfold VdiffRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet_myDiff (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end DomainTheory.NeighbourhoodSystems
