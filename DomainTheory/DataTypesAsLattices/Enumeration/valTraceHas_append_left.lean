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









theorem valTraceHas_append_left {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₁ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inl ht)⟩

end DomainTheory.DataTypesAsLattices
