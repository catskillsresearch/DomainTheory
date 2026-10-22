/-ai
If membership of a number in the value of a map on a finite set is a recursively enumerable predicate of the two indices, then the graph of the map is recursively enumerable.

The Scott-pair equation, read off an unpacked search index, is primitive recursive, and the membership clause transported along unpacking is recursively enumerable. Their conjunction, existentially quantified, is recursively enumerable. A witness unpacks to a graph clause, and a graph clause packs to a witness.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_eq_scott_pair

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.graph_of_re {f : Pomega → Pomega}
    (h : REPred fun q : ℕ × ℕ => q.2 ∈ f (e q.1)) :
    IsRE (graph f) := by
  have heq : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1 (Nat.unpair q.2).2 :=
    primrecPred_eq_scott_pair.comp
      (Primrec.pair Primrec.fst (Primrec.unpair.comp Primrec.snd))
  have hmem : REPred fun q : ℕ × ℕ =>
      (Nat.unpair q.2).2 ∈ f (e (Nat.unpair q.2).1) :=
    h.comp (Primrec.pair
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hex : REPred fun p =>
      ∃ t, p = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        (Nat.unpair t).2 ∈ f (e (Nat.unpair t).1) :=
    REPred.exists (REPred.and heq.computablePred.to_re hmem)
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, hm⟩
  · intro ⟨n, m, hm, hmem'⟩
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simpa [Nat.unpair_pair] using hm
    · simpa [Nat.unpair_pair] using hmem'

end DomainTheory.DataTypesAsLattices
