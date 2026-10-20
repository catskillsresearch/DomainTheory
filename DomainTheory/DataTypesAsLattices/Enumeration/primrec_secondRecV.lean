module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices
















































theorem primrec_secondRecV : Primrec secondRecV :=
  primrec_applyNat.comp (Primrec.const secondRecOperatorCode) Primrec.id

end DomainTheory.DataTypesAsLattices
