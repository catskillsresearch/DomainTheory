module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem primrec_diagonalInterCode : Primrec diagonalInterCode :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const interCode) primrec_num)
    Primrec.id

end DomainTheory.DataTypesAsLattices
