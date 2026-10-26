module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_eq_scott_pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Encode a Scott-pair graph clause as a single `Nat.pair` search index. -/
theorem IsRE.graph_of_primrecRel {f : Pomega → Pomega}
    (hP : PrimrecRel fun n m : ℕ => m ∈ f (e n)) :
    IsRE (graph f) := by
  have hinner : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1 (Nat.unpair q.2).2 ∧
        (Nat.unpair q.2).2 ∈ f (e (Nat.unpair q.2).1) :=
    (primrecPred_eq_scott_pair.comp
      (Primrec.pair Primrec.fst (Primrec.unpair.comp Primrec.snd))).and
      (hP.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hex : REPred fun p =>
      ∃ t, p = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        (Nat.unpair t).2 ∈ f (e (Nat.unpair t).1) :=
    REPred.exists (p := fun p t =>
        p = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
          (Nat.unpair t).2 ∈ f (e (Nat.unpair t).1))
      hinner.computablePred.to_re
  constructor
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, hm⟩
  · intro ⟨n, m, hm, hmem⟩
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simpa [Nat.unpair_pair] using hm
    · simpa [Nat.unpair_pair] using hmem

end DomainTheory.DataTypesAsLattices
