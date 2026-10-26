
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.exists_triangle_succ

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Computable inverse of Scott pairing, equal to `unpair`. -/
def unpairComp (k : ℕ) : ℕ × ℕ :=
  let w := Nat.find (exists_triangle_succ k)
  let m := k - triangle w
  (w - m, m)

end DomainTheory.DataTypesAsLattices
