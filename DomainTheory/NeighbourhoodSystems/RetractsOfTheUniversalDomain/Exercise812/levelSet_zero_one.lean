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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- `levelSet 0 1 = ℕ`: at level `0` there is a single residue class (everything is `≡ 0 mod 1`),
and `1` (bit `0` set) selects it. This is `V`'s master neighbourhood. -/
theorem levelSet_zero_one : levelSet 0 1 = Set.univ := by
  ext n; simp [levelSet, Nat.mod_one]

end DomainTheory.NeighbourhoodSystems
