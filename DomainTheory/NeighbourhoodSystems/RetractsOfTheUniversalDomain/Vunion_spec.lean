/-ai
The neighbourhood indexed by the canonical union of n and m is the union of the neighbourhoods indexed by n and by m.

The level set coded by the raw union is nonempty, because it equals that union and the neighbourhood indexed by n is nonempty. Unfolding the canonical union and rewriting by the canonical-index formula, the canonical index acts as the identity on this nonempty code, and the level-set formula for the raw union gives the union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VunionRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_VunionRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Vunion n m` genuinely indexes `VX n ∪ VX m`**, unconditionally — `VunionRaw n m` is already
non-empty (both `VX n`, `VX m` are non-empty, `VX_nonempty`, and a union of a non-empty set with
anything is non-empty), so `canonIdx` is a no-op on it (`canonIdx_eq_self_of_nonempty`), mirroring
`Vinter_spec`'s shape but with the hypothesis discharged internally rather than assumed. -/
theorem Vunion_spec (n m : ℕ) : VX (Vunion n m) = VX n ∪ VX m := by
  have hne : (levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2).Nonempty := by
    rw [levelSet_VunionRaw]; exact (VX_nonempty n).mono Set.subset_union_left
  unfold Vunion
  rw [VX_canonIdx]
  show levelSet (canonIdx (VunionRaw n m)).unpair.1 (canonIdx (VunionRaw n m)).unpair.2 = VX n ∪ VX m
  rw [canonIdx_eq_self_of_nonempty hne, levelSet_VunionRaw]

end DomainTheory.NeighbourhoodSystems
