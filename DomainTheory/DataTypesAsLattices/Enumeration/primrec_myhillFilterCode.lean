module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.filterOp
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillFilterCode
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_num
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrec_myhillFilterCode : Primrec myhillFilterCode :=
  primrec_applyNat.comp (Primrec.const filterOp) primrec_num

end DomainTheory.DataTypesAsLattices
