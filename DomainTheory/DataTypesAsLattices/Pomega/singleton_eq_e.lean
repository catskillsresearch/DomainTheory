/-ai
The singleton of a natural number k equals the finite set coded by the power of two with exponent k.

This is the reverse of the identity that the bit-set of that power of two is the singleton of k.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e_pow2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem singleton_eq_e (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (e_pow2 k).symm

end DomainTheory.DataTypesAsLattices
