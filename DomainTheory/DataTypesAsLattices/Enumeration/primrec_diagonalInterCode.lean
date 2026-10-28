module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.interCode
public import DomainTheory.DataTypesAsLattices.Enumeration.diagonalInterCode
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_num
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_diagonalInterCode : Primrec diagonalInterCode :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const interCode) primrec_num)
    Primrec.id

end DomainTheory.DataTypesAsLattices
