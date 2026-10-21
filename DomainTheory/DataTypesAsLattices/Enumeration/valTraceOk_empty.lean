/-ai
The empty valuation trace is well formed.

Both the structural condition and the G condition quantify over entries of the empty list, and simplification shows that there is no such entry.
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


theorem valTraceOk_empty : valTraceOk [] := by
  constructor
  · intro e he
    simp at he
  · intro e he _
    simp at he

end DomainTheory.DataTypesAsLattices
