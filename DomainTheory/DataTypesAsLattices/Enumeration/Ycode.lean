module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2_surjective

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A Gödel number of `Y`, used for a Kleene-style fixed point on codes. -/
noncomputable def Ycode : ℕ :=
  (theorem_3_2_surjective Ycomb_combinatory).choose

end DomainTheory.DataTypesAsLattices
