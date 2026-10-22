/-ai
A natural number lies in the level set of level k and mask m if and only if the bit of its remainder modulo 2^k is set in m.

The two sides are the defining membership condition of the level set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_affine
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem mem_levelSet {k m n : ℕ} : n ∈ levelSet k m ↔ m.testBit (n % 2 ^ k) = true :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
