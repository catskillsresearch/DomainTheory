/-ai
The predicate valTraceStruct on value traces is primitive recursive.

Justification of an entry by a trace is a primitive recursive relation. Quantifying that relation over every entry of the trace, and identifying the two arguments, yields the predicate.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecPred_valEntryJustified

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrecPred_valTraceStruct : PrimrecPred valTraceStruct := by
  have h : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) => valEntryJustified tr e :=
    primrecPred_valEntryJustified
  exact (PrimrecRel.forall_mem_list (R := fun e tr => valEntryJustified tr e)
      (h.comp Primrec.snd Primrec.fst)).comp Primrec.id Primrec.id

end DomainTheory.DataTypesAsLattices
