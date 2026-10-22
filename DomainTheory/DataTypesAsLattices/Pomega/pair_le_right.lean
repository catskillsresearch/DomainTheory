module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_le_right (n m : ℕ) : m ≤ pair n m :=
  Nat.le_add_left _ _

end DomainTheory.DataTypesAsLattices
