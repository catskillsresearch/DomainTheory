/-ai
Applying the single generator of a list to zero yields the packed list.

This is equation 3.2 applied to the packed list and to G.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem singleGenerator_app_zero (xs : List Pomega) :
    funOf (singleGenerator xs) zeroC = packList xs :=
  eq_3_2 (packList xs) Gcomb

end DomainTheory.DataTypesAsLattices
