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

theorem primrecPred_bool {α} [Primcodable α] {f : α → Bool} (hf : Primrec f) :
    PrimrecPred fun a => f a = true :=
  Primrec.eq.comp hf (Primrec.const true)

end DomainTheory.DataTypesAsLattices
