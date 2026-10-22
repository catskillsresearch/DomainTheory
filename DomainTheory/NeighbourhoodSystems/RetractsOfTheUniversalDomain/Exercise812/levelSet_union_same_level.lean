/-ai
At one common level, the union of two level sets is the level set of the bitwise disjunction of the masks.

Membership in the union is the disjunction of the two bit tests, which is the bit test of the bitwise disjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem levelSet_union_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ ∪ levelSet k m₂ = levelSet k (m₁ ||| m₂) := by
  ext n; simp [levelSet, Nat.testBit_or]

end DomainTheory.NeighbourhoodSystems
