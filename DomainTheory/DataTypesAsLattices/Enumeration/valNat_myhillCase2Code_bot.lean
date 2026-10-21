/-ai
The numerical evaluator sends the second Myhill case code of j, n, and the bottom code to the finite set coded by j.

Rewrite by the second-case evaluation and the evaluation of the bottom code, apply equation (2.7) at bottom, and simplify the bottom element.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_botCode
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem valNat_myhillCase2Code_bot (j n : ℕ) :
    valNat (myhillCase2Code j n botCode) = e j := by
  rw [valNat_myhillCase2Code, valNat_botCode, eq_2_7_bot]
  simp [botElem]

end DomainTheory.DataTypesAsLattices
