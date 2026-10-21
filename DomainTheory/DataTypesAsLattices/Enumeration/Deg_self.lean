/-ai
Every element a belongs to its own enumeration degree.

The identity combinator built by applying S to K and then to K is combinatory, and applying it to a returns a.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Icomb_SK_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Deg_self (a : Pomega) : a ∈ Deg a :=
  ⟨Icomb_SK, .app (.app .S .K) .K, (Icomb_SK_app a).symm⟩

end DomainTheory.DataTypesAsLattices
