/-ai
Upsampling a mask from level k to a finer level k' does not change the level set it represents.

A number lies in the upsampled level set when the upsampled mask has the bit of its remainder modulo 2^{k'} set. That bit test is the original mask's test at the coarser remainder, and the coarser remainder of the finer remainder is the remainder modulo 2^k.
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
