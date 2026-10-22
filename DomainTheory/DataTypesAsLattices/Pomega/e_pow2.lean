/-ai
The finite set coded by 2^k is the singleton of k.

Extensionality and the test-bit law for a power of two give the equality.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem e_pow2 (k : ℕ) : e (2 ^ k) = {k} := by
  ext i
  simp [e, Nat.testBit_two_pow]

end DomainTheory.DataTypesAsLattices
