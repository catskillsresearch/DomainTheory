/-ai
Applying the packing of a cons cell x :: xs to the numeral 0 yields x.

This is the zero law for binary sequencing of x with the packing of the tail.
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



































theorem packList_cons_zero (x : Pomega) (xs : List Pomega) :
    funOf (packList (x :: xs)) (ofNat 0) = x :=
  seq2_app_zero x (packList xs)

end DomainTheory.DataTypesAsLattices
