module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.unionCode
public import DomainTheory.DataTypesAsLattices.Enumeration.fin
public import DomainTheory.DataTypesAsLattices.Enumeration.condCode
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillCase2Code
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrec_myhillCase2Code (j n : ℕ) : Primrec (myhillCase2Code j n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const unionCode) (Primrec.const (fin j)))
    (primrec_applyNat.comp
      (primrec_applyNat.comp
        (primrec_applyNat.comp (Primrec.const condCode) (Primrec.const n))
        (Primrec.const n))
      Primrec.id)

end DomainTheory.DataTypesAsLattices
