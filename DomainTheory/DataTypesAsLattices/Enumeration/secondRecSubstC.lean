
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Computability.primrec_realized
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_secondRecSubst

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def secondRecSubstC : Pomega :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose

namespace secondRecSubstC

theorem combinatory : IsCombinatory secondRecSubstC :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.1

theorem realizes : Realizes secondRecSubstC secondRecSubst :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.2

end secondRecSubstC

end DomainTheory.DataTypesAsLattices
