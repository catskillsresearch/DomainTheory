/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecRel_valTraceHas

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem primrecPred_valEntryJustified :
    PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) => valEntryJustified tr e := by
  have hzero : PrimrecRel fun (_ : ValTrace) (e : ℕ × ℕ × ℕ) => e.1 = 0 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hop : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) =>
      valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) :=
    primrecRel_valTraceHas.comp Primrec.fst
      (Primrec.pair
        (Primrec.fst.comp (primrec_unpairComp.comp
          (Primrec.pred.comp (Primrec.fst.comp Primrec.snd))))
        (primrec_pair.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hbit : PrimrecRel fun (i : ℕ) (q : ValTrace × ℕ × ℕ × ℕ) =>
      q.2.2.2.testBit i = false ∨ valTraceHas q.1 (unpairComp q.2.1.pred).2 i :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          Primrec.fst)).not.or
      (primrecRel_valTraceHas.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp (primrec_unpairComp.comp
            (Primrec.pred.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
          Primrec.fst))).of_eq fun _ => by
      simp [Bool.not_eq_true]
  have hForall : PrimrecRel fun (bound : ℕ) (q : ValTrace × ℕ × ℕ × ℕ) =>
      ∀ i < bound,
        q.2.2.2.testBit i = false ∨ valTraceHas q.1 (unpairComp q.2.1.pred).2 i :=
    (hbit.forall_mem_list.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd).of_eq
      fun _ => by simp
  have hbits : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) =>
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i :=
    (hForall.comp
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      Primrec.id).of_eq fun q => by
      simp
  exact hzero.or (hop.and hbits)

end DomainTheory.DataTypesAsLattices
