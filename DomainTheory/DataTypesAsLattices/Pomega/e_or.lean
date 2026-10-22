module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem e_or (n m : ℕ) : e (n ||| m) = e n ∪ e m := by
  ext k
  simp [e, Nat.testBit_or]

end DomainTheory.DataTypesAsLattices
