module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified_mono

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valTraceOk_cons {tr : ValTrace} {e : ℕ × ℕ × ℕ}
    (htr : valTraceOk tr) (hjust : valEntryJustified (e :: tr) e)
    (hg : e.1 = 0 → e.2.1 ∈ Gcomb) :
    valTraceOk (e :: tr) := by
  constructor
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hjust
    · exact valEntryJustified_mono
        (fun c m ⟨t, ht⟩ => ⟨t, List.mem_cons.mpr (Or.inr ht)⟩) (htr.1 e' he')
  · intro e' he' he0
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hg he0
    · exact htr.2 e' he' he0

end DomainTheory.DataTypesAsLattices
