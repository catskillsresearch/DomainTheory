
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperator
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def secondRecOperatorCode : ℕ :=
  (theorem_3_2.surjective secondRecOperator.combinatory).choose

end DomainTheory.DataTypesAsLattices
