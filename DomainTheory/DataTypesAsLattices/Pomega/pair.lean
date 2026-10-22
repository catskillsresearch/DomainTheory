/-ai
Scott 1976, §1. The diagonal pairing of natural numbers n and m is one half of (n + m)(n + m + 1), plus m.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst11
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst12

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1.** Diagonal pairing `(n, m) = ½(n+m)(n+m+1) + m`. -/
def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m

end DomainTheory.DataTypesAsLattices
