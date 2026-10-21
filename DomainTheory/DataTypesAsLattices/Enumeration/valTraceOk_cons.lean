/-ai
If a valuation trace is well formed, a new entry is justified in the trace extended by that entry, and a zero code on the new entry forces its member into the G combinator, then the extended trace is well formed.

An entry of the extension is the new entry, justified by hypothesis, or an old entry, whose justification transfers because every membership recorded by the original trace remains recorded after the new entry is consed. The G condition holds for the new entry by hypothesis and for an old entry by well-formedness of the original trace.
ai-/
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
