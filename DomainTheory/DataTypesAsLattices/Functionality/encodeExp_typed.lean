module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Functionality.emptyE
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Functionality.prodE
public import DomainTheory.DataTypesAsLattices.Functionality.sumE
public import DomainTheory.DataTypesAsLattices.Functionality.Ea
public import DomainTheory.DataTypesAsLattices.Functionality.kerE
public import DomainTheory.DataTypesAsLattices.Functionality.Nrel
public import DomainTheory.DataTypesAsLattices.Functionality.Nk
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.pairMed
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.iterateE
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Functionality.eraseTag
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinRel
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinGood
public import DomainTheory.DataTypesAsLattices.Functionality.plotkinE
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_tag_ne
public import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_app
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_44
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl0
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl1
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl2
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl3
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl4
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl5
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_typed_inl6
public import DomainTheory.DataTypesAsLattices.Functionality.typed_ofNat_intR
public import DomainTheory.DataTypesAsLattices.Functionality.typed_bot_botElem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem encodeExp_typed : ∀ τ : LambTerm, typed (encodeExp τ) expR := by
  intro τ
  induction τ with
  | var n =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl0 (typed_ofNat_intR n)
  | zero =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl1 typed_bot_botElem
  | succ τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl2 ih
  | pred τ ih =>
    rw [encodeExp, eq_4_44]
    exact plus7_typed_inl3 ih
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl4 ?_
    rw [typed, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
      seq4_app_three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl5 ?_
    exact (typed_pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, eq_4_44]
    refine plus7_typed_inl6 ?_
    exact (typed_pairSeq_tensorR intR expR _ _).mpr ⟨typed_ofNat_intR n, ih⟩

end DomainTheory.DataTypesAsLattices
