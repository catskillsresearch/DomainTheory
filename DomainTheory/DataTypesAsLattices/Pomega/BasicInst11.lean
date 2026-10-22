/-ai
Membership of a natural number k in the finite set coded by n is decidable, because it is the decidable test of the k-th binary digit of n.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

instance (n k : ℕ) : Decidable (k ∈ e n) :=
  inferInstanceAs (Decidable (n.testBit k))

end DomainTheory.DataTypesAsLattices
