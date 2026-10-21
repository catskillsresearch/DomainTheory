/-ai
For each fixed j and n, the map sending m to the second Myhill case code of j, n, and m is primitive recursive.

It applies the constant union code to the constant finite code of j, and then applies the conditional code to the constant n, again to the constant n, and finally to the identity. Application of codes is primitive recursive.
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


theorem primrec_myhillCase2Code (j n : ℕ) : Primrec (myhillCase2Code j n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const unionCode) (Primrec.const (fin j)))
    (primrec_applyNat.comp
      (primrec_applyNat.comp
        (primrec_applyNat.comp (Primrec.const condCode) (Primrec.const n))
        (Primrec.const n))
      Primrec.id)

end DomainTheory.DataTypesAsLattices
