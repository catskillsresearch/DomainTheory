/-ai
A membership recorded by the right summand of an appended valuation trace is recorded by the append.

The witnessing time stamp remains an entry of the right summand, and hence of the append.
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


theorem valTraceHas_append_right {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₂ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inr ht)⟩

end DomainTheory.DataTypesAsLattices
