/-ai
The filter realizer realizes the function filterNum.

This is the second half of the specification of the element chosen as a realizer of the primitive recursive function filterNum.
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




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















theorem filterRealizer_realizes : Realizes filterRealizer filterNum :=
  (primrec_realized primrec_filterNum).choose_spec.2

end DomainTheory.DataTypesAsLattices
