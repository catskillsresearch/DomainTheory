module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Common-stage certificate: a finite family of r.e. facts all halt at one `evaln` bound. -/
theorem primrecPred_common_stage (c : Code) :
    PrimrecPred fun p : ℕ × ℕ =>
      ∀ k < p.1, p.1.testBit k = false ∨ (evaln p.2 c k).isSome = true := by
  have heval : Primrec fun q : ℕ × ℕ => evaln q.2 c q.1 :=
    primrec_evaln.comp <|
      Primrec.pair (Primrec.pair Primrec.snd (Primrec.const c)) Primrec.fst
  have hR : PrimrecRel fun k q : ℕ =>
      q.unpair.1.testBit k = false ∨ (evaln q.unpair.2 c k).isSome = true :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)).not.or
      (primrecPred_bool (Primrec.option_isSome.comp
        (primrec_evaln.comp <|
          Primrec.pair
            (Primrec.pair
              (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
              (Primrec.const c))
            Primrec.fst)))).of_eq fun p => by
      simp [Bool.not_eq_true]
  refine (hR.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simp [Nat.unpair_pair]

end DomainTheory.DataTypesAsLattices
