/-ai
The successor combinator, the graph of the successor operation on Pω, is recursively enumerable.

The relation which holds of n and m when m is nonzero and bit m − 1 of n is set is primitive recursive. It is equivalent to membership of m in the successor of the finite set coded by n: the predecessor of a positive m is that witness, and the successor of a bit of n is positive and has that bit as its predecessor. The graph of successor is therefore recursively enumerable, and it agrees with the successor combinator.
ai-/
module

public import Mathlib.Computability.RE
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
  constructor
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.succSet)
      (hp.of_eq fun n m => ?_)).out.of_eq ?_
  · constructor
    · intro ⟨hm0, hbit⟩
      exact ⟨m.pred, mem_e.mpr hbit, (Nat.succ_pred_eq_of_ne_zero hm0).symm⟩
    · intro ⟨k, hk, hm⟩
      subst hm
      exact ⟨Nat.succ_ne_zero k, mem_e.mp hk⟩
  · intro p; rfl

end DomainTheory.DataTypesAsLattices
