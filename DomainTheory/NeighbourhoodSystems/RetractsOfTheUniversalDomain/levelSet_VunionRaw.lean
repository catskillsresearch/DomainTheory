/-ai
The level set coded by the raw union of n and m is the union of the neighbourhoods indexed by n and by m.

Unfold the raw union, project the paired code, and apply the symmetric form of the upsampled union formula to the levels and masks of the two canonical indices.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_myUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VunionRaw

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

set_option linter.unusedSectionVars false

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
