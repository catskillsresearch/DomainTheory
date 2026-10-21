/-ai
Interpreting the closed conditional term in any environment yields the conditional combinator.

Unfold both sides and simplify interpretation, environment extension, and function update.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem condClosed_interp (ρ : ℕ → Pomega) : interp condClosed ρ = condC := by
  unfold condClosed condC
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
