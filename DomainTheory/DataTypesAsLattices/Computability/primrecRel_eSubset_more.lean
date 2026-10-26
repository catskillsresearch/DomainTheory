module

public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_eSubset
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_e_iff
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_funOf_e_iff
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace primrecRel_eSubset

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem bit :
    PrimrecRel fun i kq : ℕ =>
      (Nat.unpair kq).1.testBit i = false ∨
        i ∈ e (Nat.unpair (Nat.unpair kq).2).1 ⬝
          e (Nat.unpair (Nat.unpair kq).2).2 :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).of_eq fun p => by
    simp [Bool.not_eq_true]

theorem funOf_e :
    PrimrecRel fun k q : ℕ =>
      e k ⊆ e (Nat.unpair q).1 ⬝ e (Nat.unpair q).2 := by
  refine (primrecRel_eSubset.bit.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simp only [Nat.unpair_pair]
  exact (eSubset_funOf_e_iff p.1 p.2.unpair.1 p.2.unpair.2).symm

end primrecRel_eSubset

end DomainTheory.DataTypesAsLattices
