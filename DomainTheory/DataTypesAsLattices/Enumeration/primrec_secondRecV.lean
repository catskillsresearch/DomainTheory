/-ai
The second recursion value code is primitive recursive.

It is the application of the constant second-recursion operator code to the identity, and application of codes is primitive recursive.
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


theorem primrec_secondRecV : Primrec secondRecV :=
  primrec_applyNat.comp (Primrec.const secondRecOperatorCode) Primrec.id

end DomainTheory.DataTypesAsLattices
