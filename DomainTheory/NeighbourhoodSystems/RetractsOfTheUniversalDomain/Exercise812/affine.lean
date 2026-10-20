module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`2^k ℕ + ℓ`** (for `ℓ < 2^k`): the residue class of `ℓ` modulo `2^k`. Automatically `∅` when
`ℓ ≥ 2^k` (no `n` can leave a remainder that large), matching Scott's side condition `ℓ < 2^k`
without needing to bake it into the definition. -/
def affine (k ℓ : ℕ) : Set ℕ := {n : ℕ | n % 2 ^ k = ℓ}

end DomainTheory.NeighbourhoodSystems
