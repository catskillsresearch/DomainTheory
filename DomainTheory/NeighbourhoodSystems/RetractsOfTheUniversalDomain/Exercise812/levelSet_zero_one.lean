/-ai
The level set at level 0 with mask 1 is the set of all natural numbers, the master neighbourhood of V.

Every natural number has remainder 0 modulo 1, and the zeroth bit of the mask 1 is set.
ai-/
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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- `levelSet 0 1 = ℕ`: at level `0` there is a single residue class (everything is `≡ 0 mod 1`),
and `1` (bit `0` set) selects it. This is `V`'s master neighbourhood. -/
theorem levelSet_zero_one : levelSet 0 1 = Set.univ := by
  ext n; simp [levelSet, Nat.mod_one]

end DomainTheory.NeighbourhoodSystems
