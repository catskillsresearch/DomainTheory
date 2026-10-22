module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem valNat_Ycode : valNat Ycode = Ycomb :=
  (theorem_3_2_surjective Ycomb_combinatory).choose_spec

end DomainTheory.DataTypesAsLattices
