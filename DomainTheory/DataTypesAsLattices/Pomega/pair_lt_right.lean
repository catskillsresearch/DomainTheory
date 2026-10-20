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
public import DomainTheory.DataTypesAsLattices.Pomega.pair_le_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem pair_lt_right (n m : ℕ) : m < pair n m + 1 :=
  Nat.lt_succ_of_le (pair_le_right n m)

end DomainTheory.DataTypesAsLattices
