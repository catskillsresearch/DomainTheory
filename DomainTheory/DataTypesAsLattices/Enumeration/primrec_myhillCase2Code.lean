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


theorem primrec_myhillCase2Code (j n : ℕ) : Primrec (myhillCase2Code j n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const unionCode) (Primrec.const (fin j)))
    (primrec_applyNat.comp
      (primrec_applyNat.comp
        (primrec_applyNat.comp (Primrec.const condCode) (Primrec.const n))
        (Primrec.const n))
      Primrec.id)

end DomainTheory.DataTypesAsLattices
