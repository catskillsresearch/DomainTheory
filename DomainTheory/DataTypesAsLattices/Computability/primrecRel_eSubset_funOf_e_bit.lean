/-ai
The relation which holds when test bit i of the first component of a packed pair kq is false, or i lies in the application of the two finite sets coded by the components of the second component, is primitive recursive.

It is the disjunction of the negated boolean test-bit predicate with membership given by primrecRel_mem_funOf_e, composed with unpairing of the second component, and rewritten by Bool.not_eq_true.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_eSubset_funOf_e_bit :
    PrimrecRel fun i kq : ℕ =>
      (Nat.unpair kq).1.testBit i = false ∨
        i ∈ e (Nat.unpair (Nat.unpair kq).2).1 ⬝
          e (Nat.unpair (Nat.unpair kq).2).2 :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).of_eq fun p => by
    simp [Bool.not_eq_true]

end DomainTheory.DataTypesAsLattices
