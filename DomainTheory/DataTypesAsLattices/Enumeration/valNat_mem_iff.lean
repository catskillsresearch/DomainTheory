/-ai
A member lies in the numerical value of a code if and only if some well-formed valuation trace records that code and that member.

Completeness of well-formed traces produces a trace from the membership. In the other direction, soundness reads a recorded triple of a well-formed trace and returns the membership.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_sound
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_complete

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem valNat_mem_iff (code member : ℕ) :
    member ∈ valNat code ↔ ∃ tr, valTraceOk tr ∧ valTraceHas tr code member :=
  ⟨valTraceOk_complete code member, fun ⟨_tr, hok, ⟨_t, ht⟩⟩ =>
    valTraceOk_sound hok ht⟩

end DomainTheory.DataTypesAsLattices
