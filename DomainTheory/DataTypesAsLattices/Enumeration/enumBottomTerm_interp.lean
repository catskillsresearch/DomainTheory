/-ai
Interpreting the bottom term in any environment yields the bottom element.

Simplify by the term, interpretation, environment extension, function update, and equation (2.14).
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem enumBottomTerm_interp (ρ : ℕ → Pomega) :
    interp enumBottomTerm ρ = botElem := by
  simp [enumBottomTerm, interp, envSet, Function.update, eq_2_14]

end DomainTheory.DataTypesAsLattices
