
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem secondRecSubstC_realizes : Realizes secondRecSubstC secondRecSubst :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.2

end DomainTheory.DataTypesAsLattices
