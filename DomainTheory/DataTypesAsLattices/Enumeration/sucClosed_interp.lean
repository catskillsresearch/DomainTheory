/-ai
Interpreting the closed successor term in any environment yields the successor combinator.

Unfolding the term and the combinator, the interpretation, the environment, and the function update simplify to the same element.
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

























































theorem sucClosed_interp (ρ : ℕ → Pomega) : interp sucClosed ρ = sucC := by
  unfold sucClosed sucC
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
