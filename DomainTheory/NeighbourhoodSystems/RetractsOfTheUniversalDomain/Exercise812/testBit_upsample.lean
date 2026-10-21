/-ai
For a residue r strictly below 2^{k'}, the bit r of an upsampled mask is set if and only if the bit of r modulo 2^k is set in the original mask.

Unfold the sum-of-powers definition of upsampling. The bit r is set exactly when r is a bit index of that sum, hence when r lies in the finite set of residues below 2^{k'} whose coarser bit is set. The bound on r places it in that range, leaving the coarser bit test.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.upsample

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem testBit_upsample {k k' m r : ℕ} (hr : r < 2 ^ k') :
    (upsample k k' m).testBit r ↔ m.testBit (r % 2 ^ k) := by
  unfold upsample
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow,
    Finset.mem_filter, Finset.mem_range]
  simp [hr]

end DomainTheory.NeighbourhoodSystems
