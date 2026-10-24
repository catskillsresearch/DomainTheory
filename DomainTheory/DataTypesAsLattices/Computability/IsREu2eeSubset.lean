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
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_common_stage
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_iff_stage

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Finite inclusion `e n ⊆ x` is r.e. in `n` when `x` is, via one common `evaln` stage. -/
theorem IsRE.eSubset {x : Pomega} (hx : IsRE x) :
    REPred fun n => e n ⊆ x := by
  have hf : Partrec fun k : ℕ =>
      (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) :=
    hx.out.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hex : REPred fun n =>
      ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true :=
    REPred.exists (p := fun n s =>
        ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true)
      (primrecPred_common_stage c).computablePred.to_re
  exact hex.of_eq fun n => (eSubset_iff_stage hc n).symm

end DomainTheory.DataTypesAsLattices
