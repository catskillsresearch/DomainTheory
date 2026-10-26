module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.predC_app
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
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
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredSet
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredC
public import DomainTheory.DataTypesAsLattices.Computability.primrec_realized
public import DomainTheory.DataTypesAsLattices.Computability.primrec_enumFun
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC_eq

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


/-- **Scott 1976, Appendix.** Every r.e. element belongs to the
combinatory closure. -/
theorem IsRE.combinatory {u : Pomega} (hu : IsRE u) : IsCombinatory u := by
  have hpart : Partrec fun k : ℕ =>
      Part.assert (k ∈ u) fun _ => Part.some (0 : ℕ) :=
    hu.out.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hpart)
  obtain ⟨r, hr, hreal⟩ := primrec_realized (primrec_enumFun c)
  have hrange := enumRangeC_eq hreal
  have hpred : DataTypesAsLattices.predSet (enumRangeC r) = u := by
    ext n
    constructor
    · intro hn
      rw [hrange] at hn
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hn
      have heq : enumFun c t = n + 1 := by simpa [ofNat] using ht.symm
      have hs : (evaln t.unpair.2 c t.unpair.1).isSome = true := by
        by_contra h
        have : (evaln t.unpair.2 c t.unpair.1).isSome = false :=
          Bool.eq_false_of_not_eq_true h
        simp [enumFun, this] at heq
      have hfirst : t.unpair.1 = n := by
        simp [enumFun, hs] at heq
        omega
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      have hmem : v ∈ Code.eval c t.unpair.1 :=
        evaln_sound (by simpa [Option.mem_def] using hv)
      rw [hc] at hmem
      simpa [hfirst] using (Part.mem_assert_iff.mp hmem).1
    · intro hn
      have hmem : 0 ∈ Code.eval c n := by
        rw [hc]
        exact Part.mem_assert_iff.mpr ⟨hn, Part.mem_some_iff.mpr rfl⟩
      obtain ⟨s, hs⟩ := evaln_complete.mp hmem
      rw [hrange]
      refine Set.mem_iUnion.mpr ⟨Nat.pair n s, ?_⟩
      have hsome : (evaln s c n).isSome = true := Option.isSome_of_mem hs
      simp [enumFun, Nat.unpair_pair, hsome, ofNat]
  have hcomb : IsCombinatory (DataTypesAsLattices.predC ⬝ enumRangeC r) :=
    .app .pred (enumRangeC_combinatory hr)
  rw [DataTypesAsLattices.predC_app, hpred] at hcomb
  exact hcomb

end DomainTheory.DataTypesAsLattices
