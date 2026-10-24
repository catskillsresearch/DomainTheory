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
public import DomainTheory.DataTypesAsLattices.Computability.composeC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.composeC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.constComb_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.constComb_realizes
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_realizes
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer_realizes
public import DomainTheory.DataTypesAsLattices.Computability.precC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.precC_realizes

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


/-- Every unary primitive-recursive function has a combinatory realizer. -/
theorem primrec_realized {p : ℕ → ℕ} (hp : Nat.Primrec p) :
    ∃ u, IsCombinatory u ∧ Realizes u p := by
  induction hp with
  | zero =>
      exact ⟨constComb 0, constComb_combinatory 0, constComb_realizes 0⟩
  | succ =>
      exact ⟨sucC, .suc, fun n => by rw [sucC_app, succSet_ofNat]⟩
  | left =>
      exact ⟨unpairFstC, unpairFstC_combinatory, unpairFstC_realizes⟩
  | right =>
      exact ⟨unpairSndC, unpairSndC_combinatory, unpairSndC_realizes⟩
  | pair _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨pairRealizer u v, pairRealizer_combinatory hu hv,
        pairRealizer_realizes hru hrv⟩
  | comp _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨composeC u v, composeC_combinatory hu hv, composeC_realizes hru hrv⟩
  | prec _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨precC u v, precC_combinatory hu hv, precC_realizes hru hrv⟩

end DomainTheory.DataTypesAsLattices
