module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_num
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubst

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_secondRecSubst : Primrec secondRecSubst :=
  primrec_applyNat.comp Primrec.id primrec_num

end DomainTheory.DataTypesAsLattices
