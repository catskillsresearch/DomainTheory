/-ai
The relation that a value trace records a given code and value is primitive recursive.

Existence, among the entries of the trace, of an entry whose first component equals the code and whose second component's first part equals the value is primitive recursive, as a list-bounded existence of a conjunction of equalities. That existence agrees with the characterization of the recording relation.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_iff

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
  exact h.of_eq fun tr p => (valTraceHas_iff tr p.1 p.2).symm

end DomainTheory.DataTypesAsLattices
