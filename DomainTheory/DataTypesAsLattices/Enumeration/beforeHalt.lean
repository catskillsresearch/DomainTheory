/-ai
The relation beforeHalt of a natural number m and an index j asserts that every index strictly below j + 1 has halt enumeration different from m.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def beforeHalt (m j : ℕ) : Prop := ∀ i < j + 1, haltEnum i ≠ m

end DomainTheory.DataTypesAsLattices
