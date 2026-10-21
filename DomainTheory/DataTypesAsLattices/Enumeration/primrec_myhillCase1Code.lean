/-ai
For each fixed n, the map sending m to the first Myhill case code of n and m is primitive recursive.

It is the application of the constant intersection code to the constant n, applied again to the Myhill filter code, and application of codes is primitive recursive.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
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
