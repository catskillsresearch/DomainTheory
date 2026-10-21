/-ai
The level set of level k and mask m is the union of the residue classes of those residues ℓ below 2^k whose bit is set in m.

If a number lies in the level set, its remainder modulo 2^k is such a residue, and the number lies in that residue class. Conversely, a number in a selected residue class has remainder equal to that residue, so the corresponding bit of the mask is set.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- `levelSet k m` is exactly the union of `affine k ℓ` over `ℓ` with `m.testBit ℓ`. -/
theorem levelSet_eq_biUnion (k m : ℕ) :
    levelSet k m = ⋃ ℓ ∈ (Finset.range (2 ^ k)).filter (fun ℓ => m.testBit ℓ), affine k ℓ := by
  ext n
  simp only [mem_levelSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, mem_affine,
    exists_prop]
  constructor
  · intro h; exact ⟨n % 2 ^ k, ⟨Nat.mod_lt n (by positivity), h⟩, rfl⟩
  · rintro ⟨ℓ, ⟨-, hm⟩, rfl⟩; exact hm

end DomainTheory.NeighbourhoodSystems
