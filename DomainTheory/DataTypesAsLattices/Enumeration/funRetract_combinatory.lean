/-ai
The function-space retract is combinatory.

Rewrite it as the interpretation of the closed function-retract term, and apply the closed case of theorem 2.4.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.funRetractTerm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem funRetract_combinatory : IsCombinatory funRetract := by
  rw [← funRetractTerm_interp]
  exact theorem_2_4_closed funRetractTerm

end DomainTheory.DataTypesAsLattices
