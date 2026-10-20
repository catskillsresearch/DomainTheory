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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.testBit_upsample

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`upsample` preserves the set `levelSet` represents.** -/
theorem levelSet_upsample {k k' m : ℕ} (hk : k ≤ k') : levelSet k' (upsample k k' m) = levelSet k m := by
  ext n
  simp only [mem_levelSet]
  rw [testBit_upsample (Nat.mod_lt n (by positivity)),
    Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hk)]

end DomainTheory.NeighbourhoodSystems
