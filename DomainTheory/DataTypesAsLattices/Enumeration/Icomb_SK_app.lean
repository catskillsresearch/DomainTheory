/-ai
Applying the identity combinator built from S and K to any element x returns x.

Unfold the definition and rewrite by the beta law for S, then by the beta law for K.
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

































theorem Icomb_SK_app (x : Pomega) : funOf Icomb_SK x = x := by
  rw [Icomb_SK, Scomb_beta3, Kcomb_beta2]

end DomainTheory.DataTypesAsLattices
