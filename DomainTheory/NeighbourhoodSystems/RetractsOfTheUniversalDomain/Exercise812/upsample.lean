/-ai
Upsampling rewrites a level-k mask at a level k' as the natural number whose set bits are the residues r below 2^{k'} for which the bit of r modulo 2^k is set in the original mask. It is the sum of the corresponding powers of two.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_affine
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_levelSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Re-express a level-`k` bitmask `m` at a finer level `k' ≥ k`: residue `r` (mod `2^k'`) is
included iff `r`'s coarser residue `r % 2^k` was. Built via `Nat.equivBitIndices` (the bijection
`ℕ ≃ Finset ℕ` sending `n` to its set bits) rather than raw shifting arithmetic. -/
def upsample (k k' m : ℕ) : ℕ :=
  ∑ r ∈ (Finset.range (2 ^ k')).filter (fun r => m.testBit (r % 2 ^ k)), 2 ^ r

end DomainTheory.NeighbourhoodSystems
