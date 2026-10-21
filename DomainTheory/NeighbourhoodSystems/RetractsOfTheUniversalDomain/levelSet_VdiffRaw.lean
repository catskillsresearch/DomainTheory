/-ai
The level set coded by the raw difference of n and m is the set difference of the neighbourhoods indexed by n and by m.

Unfold the raw difference, project the paired code, and apply the symmetric form of the upsampled difference formula to the levels and masks of the two canonical indices.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_myDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw

@[expose] public section

set_option linter.unusedSectionVars false

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
