module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.interCode
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillCase1Code
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillFilterCode

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrec_myhillCase1Code (n : ℕ) : Primrec (myhillCase1Code n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const interCode) (Primrec.const n))
    primrec_myhillFilterCode

end DomainTheory.DataTypesAsLattices
