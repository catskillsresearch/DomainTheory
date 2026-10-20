module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_affine
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.upsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_upsample

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`levelSet` is closed under intersection, unconditionally** (unlike `Definition87.lean`'s `U`,
which genuinely needs a consistency hypothesis): upsample both masks to the common level
`max k₁ k₂` and take the bitwise `AND`. -/
theorem levelSet_inter (k₁ m₁ k₂ m₂ : ℕ) :
    levelSet k₁ m₁ ∩ levelSet k₂ m₂
      = levelSet (max k₁ k₂) (upsample k₁ (max k₁ k₂) m₁ &&& upsample k₂ (max k₁ k₂) m₂) := by
  rw [← levelSet_upsample (le_max_left k₁ k₂) (m := m₁), ← levelSet_upsample (le_max_right k₁ k₂) (m := m₂)]
  ext n
  simp only [mem_levelSet, Set.mem_inter_iff, Nat.testBit_and, Bool.and_eq_true]

end DomainTheory.NeighbourhoodSystems
