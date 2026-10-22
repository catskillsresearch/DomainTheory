/-ai
The residue class of ℓ modulo 2^k equals the level set at level k whose mask is the single power of two 2^ℓ.

A number lies in the residue class when its remainder equals ℓ, and the single-bit test of that mask holds at exactly that remainder.
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


/-- `affine k ℓ` itself is the singleton-bitmask `levelSet`. -/
theorem affine_eq_levelSet (k ℓ : ℕ) : affine k ℓ = levelSet k (2 ^ ℓ) := by
  ext n
  simp [mem_affine, mem_levelSet, Nat.testBit_two_pow, eq_comm]

end DomainTheory.NeighbourhoodSystems
