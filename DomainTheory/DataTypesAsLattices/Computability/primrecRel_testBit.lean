module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_testBit : PrimrecRel fun n k : ℕ => n.testBit k = true :=
  primrecPred_bool (f := fun p : ℕ × ℕ => p.1.testBit p.2) primrec_testBit

end DomainTheory.DataTypesAsLattices
