
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2
public import DomainTheory.DataTypesAsLattices.Enumeration.unionOperator_combinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- One fixed Gödel code for the binary union operator. -/
noncomputable def unionCode : ℕ :=
  (theorem_3_2.surjective unionOperator_combinatory).choose

end DomainTheory.DataTypesAsLattices
