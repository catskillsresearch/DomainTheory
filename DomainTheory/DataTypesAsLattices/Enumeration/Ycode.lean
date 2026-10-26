module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A Gödel number of `Y`, used for a Kleene-style fixed point on codes. -/
noncomputable def Ycode : ℕ :=
  (theorem_3_2.surjective Ycomb.combinatory).choose

end DomainTheory.DataTypesAsLattices
