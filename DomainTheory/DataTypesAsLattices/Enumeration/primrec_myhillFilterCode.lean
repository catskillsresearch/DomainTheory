/-ai
The Myhill filter code is primitive recursive.

It is the application of the constant filter-operator code to the numeral code, and application of codes is primitive recursive.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrec_myhillFilterCode : Primrec myhillFilterCode :=
  primrec_applyNat.comp (Primrec.const filterOp) primrec_num

end DomainTheory.DataTypesAsLattices
