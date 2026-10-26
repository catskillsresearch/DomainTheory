module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrecRel_valTraceHas :
    PrimrecRel fun (tr : ValTrace) (p : ℕ × ℕ) => valTraceHas tr p.1 p.2 := by
  have h : PrimrecRel fun (tr : ValTrace) (p : ℕ × ℕ) =>
      ∃ e ∈ tr, e.1 = p.1 ∧ e.2.1 = p.2 :=
    PrimrecRel.exists_mem_list
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)).and
        (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun tr p => (valTraceHas.iff tr p.1 p.2).symm

end DomainTheory.DataTypesAsLattices
