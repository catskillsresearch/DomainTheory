module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.pair_le_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_lt_left (n m : ℕ) : n < pair n m + 1 :=
  Nat.lt_succ_of_le (pair_le_left n m)

end DomainTheory.DataTypesAsLattices
