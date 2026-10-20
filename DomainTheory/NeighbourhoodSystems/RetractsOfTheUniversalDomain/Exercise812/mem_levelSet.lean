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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem mem_levelSet {k m n : ℕ} : n ∈ levelSet k m ↔ m.testBit (n % 2 ^ k) = true :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
