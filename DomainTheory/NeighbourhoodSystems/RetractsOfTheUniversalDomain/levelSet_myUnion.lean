/-ai
The union of two level sets equals the level set, at the maximum of the two levels, of the bitwise disjunction of the two masks upsampled to that level.

On the left-hand side, replace each level set by its upsampling to the maximum level. Then apply the same-level union formula and the equation for the bitwise disjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Computable version of `levelSet_union_same_level` at differing levels** — the bitwise-`OR`
analogue of `levelSet_myInter`, mirroring its proof verbatim with `myLor`/`Nat.testBit_or` in place
of `myLand`/`Nat.testBit_and`. -/
theorem levelSet_myUnion (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∪ levelSet k2 m2
      = levelSet (max k1 k2) (myLor (myUpsample k1 (max k1 k2) m1) (myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet_myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet_union_same_level, myLor_eq_lor]

end DomainTheory.NeighbourhoodSystems
