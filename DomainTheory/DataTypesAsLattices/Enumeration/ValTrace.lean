/-ai
A value trace is a finite list of triples of natural numbers. It records a finite derivation that a member belongs to the value of a code, with the application witness stored on positive codes.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Finite derivation that `member ∈ valNat code`, with the application
witness `t` stored on positive codes. -/
abbrev ValTrace := List (ℕ × ℕ × ℕ)

end DomainTheory.DataTypesAsLattices
