/-ai
The append of two well-formed valuation traces is well formed.

An entry of the append lies in one of the two summands. Its structural justification transfers to the append because a membership recorded by either summand remains recorded after appending on the left or on the right. The G condition of the entry likewise follows from the G condition in the summand that contains it.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_left
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_right
public import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified_mono

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valTraceOk_append {tr₁ tr₂ : ValTrace}
    (h₁ : valTraceOk tr₁) (h₂ : valTraceOk tr₂) :
    valTraceOk (tr₁ ++ tr₂) := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_left) (h₁.1 e he)
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_right) (h₂.1 e he)
  · intro e he he0
    rcases List.mem_append.mp he with he | he
    · exact h₁.2 e he he0
    · exact h₂.2 e he he0

end DomainTheory.DataTypesAsLattices
