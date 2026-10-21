/-ai
Interpreting the closed predecessor term in any environment yields the predecessor combinator.

Unfold both sides and simplify the interpretation and the environment update.
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

























































theorem predClosed_interp (ρ : ℕ → Pomega) : interp predClosed ρ = predC := by
  unfold predClosed predC
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
