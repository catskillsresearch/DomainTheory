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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, after (2.2).** `⊤ = ω`. -/
def topElem : Pomega := Set.univ

end DomainTheory.DataTypesAsLattices
