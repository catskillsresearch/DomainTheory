/-ai
If a set is recursively enumerable, then the predicate that zero lies in it is recursively enumerable.

It is the recursively enumerable membership predicate composed with the constant function with value zero.
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

theorem IsRE.hasZero {z : Pomega} (hz : IsRE z) : REPred fun _ : ℕ => 0 ∈ z :=
  hz.comp (Computable.const 0)

end DomainTheory.DataTypesAsLattices
