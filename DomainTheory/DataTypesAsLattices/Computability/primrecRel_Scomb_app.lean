module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsComputable
public import DomainTheory.DataTypesAsLattices.Computability.LambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj4
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.Realizes2
public import DomainTheory.DataTypesAsLattices.Computability.composeC
public import DomainTheory.DataTypesAsLattices.Computability.constComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Computability.addStepC
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.safePredC
public import DomainTheory.DataTypesAsLattices.Computability.subStepC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.pairTerm
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter
public import DomainTheory.DataTypesAsLattices.Computability.sqrtEnv
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepTerm
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSquareTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairDeltaTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairTestTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpEnv
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpTerm
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer
public import DomainTheory.DataTypesAsLattices.Computability.precEnv
public import DomainTheory.DataTypesAsLattices.Computability.precTerm
public import DomainTheory.DataTypesAsLattices.Computability.precC
public import DomainTheory.DataTypesAsLattices.Computability.enumFun
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC
public import DomainTheory.DataTypesAsLattices.Computability.ComputableFin
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_funOf_e_iff
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj4
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_Scomb_subset

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem primrecRel_Scomb_app :
    PrimrecRel fun k t : ℕ =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t) := by
  have hmem : PrimrecPred fun p : ℕ × ℕ =>
      pair p.1 (pack4_proj4 p.2) ∈
        e (pack4_proj1 p.2) ⬝ e (pack4_proj3 p.2) :=
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp (primrec_pack4_proj1.comp Primrec.snd)
        (primrec_pack4_proj3.comp Primrec.snd))
      (primrec_pair.comp Primrec.fst (primrec_pack4_proj4.comp Primrec.snd))).of_eq
      fun p => by simp [Nat.unpair_pair]
  refine (primrecPred_Scomb_subset.and hmem).of_eq fun p => ?_
  constructor
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mpr hs, hm⟩
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mp hs, hm⟩

end DomainTheory.DataTypesAsLattices
