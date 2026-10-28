module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

abbrev ValTrace := List (ℕ × ℕ × ℕ)

end DomainTheory.DataTypesAsLattices
