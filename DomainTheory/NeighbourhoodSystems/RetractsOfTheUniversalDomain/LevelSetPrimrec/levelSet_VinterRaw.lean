module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myInter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`VinterRaw` realizes `VX n ∩ VX m`** at the `levelSet` level (unconditionally — `V`'s
consistency is genuinely automatic, mirroring `PN`). -/
theorem levelSet_VinterRaw (n m : ℕ) :
    levelSet (VinterRaw n m).unpair.1 (VinterRaw n m).unpair.2 = VX n ∩ VX m := by
  unfold VinterRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet_myInter (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end DomainTheory.NeighbourhoodSystems
