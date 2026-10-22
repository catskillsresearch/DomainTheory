/-ai
One fixed Gödel code for the binary union operator is a natural number chosen, by surjectivity of Scott's enumeration, so that its value is the combinatory graph of binary union.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2_surjective
public import DomainTheory.DataTypesAsLattices.Enumeration.unionOperator_combinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- One fixed Gödel code for the binary union operator. -/
noncomputable def unionCode : ℕ :=
  (theorem_3_2_surjective unionOperator_combinatory).choose

end DomainTheory.DataTypesAsLattices
