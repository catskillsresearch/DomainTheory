/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
import DomainTheory.DataTypesAsLattices.Computability.mem_condC_iff


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.condC : IsRE condC := by
  have heq : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1
        (pair (Nat.unpair (Nat.unpair q.2).2).1
          (pair (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)) :=
    Primrec.eq.comp Primrec.fst
      (primrec_pair.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (primrec_pair.comp
          (Primrec.fst.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
          (primrec_pair.comp
            (Primrec.fst.comp (Primrec.unpair.comp
              (Primrec.snd.comp (Primrec.unpair.comp
                (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))
            (Primrec.snd.comp (Primrec.unpair.comp
              (Primrec.snd.comp (Primrec.unpair.comp
                (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))))
  have hbit0 : PrimrecPred fun q : ℕ × ℕ =>
      (Nat.unpair q.2).1.testBit
          (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
        (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1.testBit 0 = true :=
    (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))).and
      (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))
        (Primrec.const 0)))
  have hbit1 : PrimrecPred fun q : ℕ × ℕ =>
      (Nat.unpair (Nat.unpair q.2).2).1.testBit
          (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
        2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1 :=
    (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))).and
      (Primrec.nat_le.comp (Primrec.const 2)
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))
  have hinner : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1
          (pair (Nat.unpair (Nat.unpair q.2).2).1
            (pair (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1
              (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)) ∧
        (((Nat.unpair q.2).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
            (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1.testBit 0 =
              true) ∨
          ((Nat.unpair (Nat.unpair q.2).2).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
            2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1)) :=
    heq.and (hbit0.or hbit1)
  have hex : REPred fun p =>
      ∃ t, p = pair (Nat.unpair t).1
          (pair (Nat.unpair (Nat.unpair t).2).1
            (pair (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1
              (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2)) ∧
        (((Nat.unpair t).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2 = true ∧
            (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1.testBit 0 =
              true) ∨
          ((Nat.unpair (Nat.unpair t).2).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2 = true ∧
            2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1)) :=
    REPred.exists hinner.computablePred.to_re
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact (mem_condC_iff p).mpr
      ⟨(Nat.unpair t).1, (Nat.unpair (Nat.unpair t).2).1,
        (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1,
        (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2, ht, hm⟩
  · intro hp
    obtain ⟨n0, n1, n2, m, ht, hm⟩ := (mem_condC_iff p).mp hp
    refine ⟨Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m)), ?_, ?_⟩
    · simpa [Nat.unpair_pair] using ht
    · simpa [Nat.unpair_pair] using hm

end DomainTheory.DataTypesAsLattices
