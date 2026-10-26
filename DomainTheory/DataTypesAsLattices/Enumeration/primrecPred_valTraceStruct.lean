module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceStruct
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
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
