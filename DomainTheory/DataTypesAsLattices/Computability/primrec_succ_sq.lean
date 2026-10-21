/-ai
The function sending k to (k + 1) · (k + 1) is primitive recursive.

It is the product of the successor of the identity function with itself.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrec_succ_sq : Primrec fun k : ℕ => (k + 1) * (k + 1) :=
  Primrec.nat_mul.comp (Primrec.succ.comp Primrec.id) (Primrec.succ.comp Primrec.id)

end DomainTheory.DataTypesAsLattices
