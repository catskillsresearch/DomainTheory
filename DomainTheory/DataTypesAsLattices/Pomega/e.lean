module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Pomega
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1.** Finite set coded by the binary expansion of `n`. -/
def e (n : ℕ) : Pomega := {k | n.testBit k}

end DomainTheory.DataTypesAsLattices
