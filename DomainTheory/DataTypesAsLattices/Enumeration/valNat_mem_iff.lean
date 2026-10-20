module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
