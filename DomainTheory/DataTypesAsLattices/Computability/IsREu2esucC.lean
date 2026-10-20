module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2esuccSet
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2egraph_of_primrecRel

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.sucC : IsRE sucC := by
  have hp : PrimrecRel fun n m : ℕ => m ≠ 0 ∧ n.testBit m.pred = true :=
    (PrimrecPred.not (Primrec.eq.comp Primrec.snd (Primrec.const 0))).and
      (primrecPred_bool
        (Primrec₂.comp primrec_testBit Primrec.fst (Primrec.pred.comp Primrec.snd)))
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.succSet)
      (hp.of_eq fun n m => ?_)).of_eq ?_
  · constructor
    · intro ⟨hm0, hbit⟩
      exact ⟨m.pred, mem_e.mpr hbit, (Nat.succ_pred_eq_of_ne_zero hm0).symm⟩
    · intro ⟨k, hk, hm⟩
      subst hm
      exact ⟨Nat.succ_ne_zero k, mem_e.mp hk⟩
  · intro p; rfl

end DomainTheory.DataTypesAsLattices
