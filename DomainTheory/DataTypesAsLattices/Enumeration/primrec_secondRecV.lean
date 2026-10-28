module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperatorCode
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecV
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_secondRecV : Primrec secondRecV :=
  primrec_applyNat.comp (Primrec.const secondRecOperatorCode) Primrec.id

end DomainTheory.DataTypesAsLattices
