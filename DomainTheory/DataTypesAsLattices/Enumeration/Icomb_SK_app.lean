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


theorem Icomb_SK_app (x : Pomega) : funOf Icomb_SK x = x := by
  rw [Icomb_SK, Scomb_beta3, Kcomb_beta2]

end DomainTheory.DataTypesAsLattices
