module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **The "same level" set-difference formula**, mirroring `Exercise812.lean`'s
`levelSet_inter_same_level` exactly (`&&&` becomes the "and-not" combinator `a ^^^ (a &&& b)`,
via `testBit_xor_and_self`). -/
theorem levelSet_diff_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ \ levelSet k m₂ = levelSet k (m₁ ^^^ (m₁ &&& m₂)) := by
  ext n; simp [levelSet]

end DomainTheory.NeighbourhoodSystems
