
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperator
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A Gödel code for the uniform operator in Theorem 3.3. -/
noncomputable def secondRecOperatorCode : ℕ :=
  (theorem_3_2.surjective secondRecOperator.combinatory).choose

end DomainTheory.DataTypesAsLattices
