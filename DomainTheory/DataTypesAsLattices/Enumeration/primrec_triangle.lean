module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrec_triangle : Primrec triangle :=
  (Primrec.nat_div.comp
    (Primrec.nat_mul.comp Primrec.id (Primrec.succ.comp Primrec.id))
    (Primrec.const 2)).of_eq fun _ => rfl

end DomainTheory.DataTypesAsLattices
