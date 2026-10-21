/-ai
The predecessor combinator is recursively enumerable.

The relation that bit m + 1 of n is set is primitive recursive, by a boolean test of the test-bit function on the successor of the second argument. That relation agrees in both directions with membership of m in the predecessor of the finite set e n, by the bit characterization of e. The graph of the predecessor operation is therefore recursively enumerable, and that graph is the predecessor combinator.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredSet
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2egraph_of_primrecRel

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.predC : IsRE predC := by
  have hp : PrimrecRel fun n m : ℕ => n.testBit (m + 1) = true :=
    primrecPred_bool (Primrec₂.comp primrec_testBit Primrec.fst (Primrec.succ.comp Primrec.snd))
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.predSet)
      (hp.of_eq fun n m => ?_)).of_eq ?_
  · constructor
    · intro h; exact mem_e.mpr h
    · intro h; exact mem_e.mp h
  · intro p; rfl

end DomainTheory.DataTypesAsLattices
