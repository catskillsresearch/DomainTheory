/-ai
The conditional combinator is recursively enumerable.

The equation that unpacks a nested pair into four components is primitive recursive, as are the two bit conditions: one test bit conjoined with a test of bit zero, and the other test bit conjoined with a lower bound of two. Their disjunction, conjoined with the unpacking equation, is primitive recursive, and existential quantification makes it recursively enumerable. A witness unpacks, by the membership characterization of the conditional combinator, to four indices satisfying one of the two bit conditions, and four such indices pack as a nested pair to a witness.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.mem_condC_iff

@[expose] public section


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
  constructor
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
