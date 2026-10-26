module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.hasZero {z : Pomega} (hz : IsRE z) : REPred fun _ : ℕ => 0 ∈ z :=
  hz.out.comp (Computable.const 0)

end DomainTheory.DataTypesAsLattices
