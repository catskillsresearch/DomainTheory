/-ai
The relation between i and a packed pair kt which holds when test bit i of the first component of kt is false, or i lies in the application of the finite set coded by pack4_proj2 of the second component to the finite set coded by pack4_proj3 of the second component, is primitive recursive.

It is the disjunction of the negated boolean test-bit predicate with membership given by primrecRel_mem_funOf_e, composed with the unpairings and pack4 projections of the second component, and rewritten by Bool.not_eq_true.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrecRel_Scomb_bit :
    PrimrecRel fun i kt : ℕ =>
      (Nat.unpair kt).1.testBit i = false ∨
        i ∈ e (pack4_proj2 (Nat.unpair kt).2) ⬝
          e (pack4_proj3 (Nat.unpair kt).2) :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp
        (primrec_pack4_proj2.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
        (primrec_pack4_proj3.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      Primrec.fst)).of_eq fun p => by simp [Bool.not_eq_true]

end DomainTheory.DataTypesAsLattices
