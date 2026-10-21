/-ai
The diagonal intersection code is primitive recursive.

It is the application of the constant intersection code to the numeral code, applied again to the identity, and application of codes is primitive recursive.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
