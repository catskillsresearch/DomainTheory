module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Retracts.comp
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
  constructor
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.predSet)
      (hp.of_eq fun n m => ?_)).out.of_eq ?_
  · constructor
    · intro h; exact mem_e.mpr h
    · intro h; exact mem_e.mp h
  · intro p; rfl

end DomainTheory.DataTypesAsLattices
