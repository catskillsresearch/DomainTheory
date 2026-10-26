module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.bot_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def botCode : ℕ :=
  (theorem_3_2.surjective bot_combinatory).choose

end DomainTheory.DataTypesAsLattices
