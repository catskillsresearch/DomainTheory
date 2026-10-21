/-ai
Interpreting the term gClosed in any environment yields the combinator G.

Unfold both sides. The graphs agree after rewriting by the interpretation of gpackClosed and simplifying the environment update and the zero combinator.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.gpackClosed_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



























































theorem gClosed_interp (ρ : ℕ → Pomega) : interp gClosed ρ = Gcomb := by
  unfold gClosed Gcomb
  apply congrArg graph
  funext z
  simp only [interp]
  rw [gpackClosed_interp]
  simp [envSet, Function.update, zeroC]

end DomainTheory.DataTypesAsLattices
