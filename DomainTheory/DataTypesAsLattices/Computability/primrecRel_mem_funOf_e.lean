module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.primrec_twoPow
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_eSubset
public import DomainTheory.DataTypesAsLattices.Computability.mem_funOf_e_iff

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Retracts.comp
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_mem_funOf_e :
    PrimrecRel fun q m : ℕ =>
      m ∈ e (Nat.unpair q).1 ⬝ e (Nat.unpair q).2 := by
  have hinner : PrimrecRel fun n packed : ℕ =>
      e n ⊆ e (Nat.unpair (Nat.unpair packed).1).2 ∧
        (Nat.unpair (Nat.unpair packed).1).1.testBit
          (pair n (Nat.unpair packed).2) :=
    ((primrecRel_eSubset.comp Primrec.fst
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))).and
      (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
        (primrec_pair.comp Primrec.fst
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))
  refine (hinner.exists_lt.comp
      (primrec_twoPow.comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))))
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq
    fun q => ?_
  simp only [Nat.unpair_pair]
  exact (mem_funOf_e_iff q.1.unpair.1 q.1.unpair.2 q.2).symm

end DomainTheory.DataTypesAsLattices
