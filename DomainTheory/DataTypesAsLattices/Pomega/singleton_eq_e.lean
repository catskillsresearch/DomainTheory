module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e_pow2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem singleton_eq_e (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (e_pow2 k).symm

end DomainTheory.DataTypesAsLattices
