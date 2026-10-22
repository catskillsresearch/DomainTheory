/-ai
Interpreting the closed K term in any environment yields the K combinator.

Unfold both sides and simplify the interpretation and the environment update.
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


theorem kClosed_interp (ρ : ℕ → Pomega) : interp kClosed ρ = Kcomb := by
  unfold kClosed Kcomb
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
