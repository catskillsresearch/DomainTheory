module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e
public import DomainTheory.DataTypesAsLattices.Pomega.two_pow_le_of_testBit
public import DomainTheory.DataTypesAsLattices.Pomega.le_two_pow

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem mem_e_le {n k : ℕ} (h : k ∈ e n) : k ≤ n :=
  (le_two_pow k).trans (two_pow_le_of_testBit h)

end DomainTheory.DataTypesAsLattices
