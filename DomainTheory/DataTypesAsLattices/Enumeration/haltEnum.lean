module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Shifted enumerator of the halting set: `0` is the miss marker. -/
def haltEnum (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome
    then t.unpair.1 + 1 else 0

end DomainTheory.DataTypesAsLattices
