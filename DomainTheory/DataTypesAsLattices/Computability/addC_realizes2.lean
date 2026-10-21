/-ai
The addition combinator realizes addition of natural numbers.

Simplify by the application equation for the addition combinator, the evaluation of primitive recursion on numerals, and the value of that recursion for addition.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.primRecVal_add
public import DomainTheory.DataTypesAsLattices.Computability.addC_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem addC_realizes2 : Realizes2 addC fun n m => n + m := fun n m => by
  simp [addC_app, primRecComb_ofNat, primRecVal_add]

end DomainTheory.DataTypesAsLattices
