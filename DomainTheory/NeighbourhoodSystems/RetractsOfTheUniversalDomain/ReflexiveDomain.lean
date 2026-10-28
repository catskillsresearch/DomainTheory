module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbedIntoPow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ExampleC_le_B
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.FixOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.CoupledFixedPoints
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SumProdRetracts
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_15
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511
variable {α : Type*} (V : NeighborhoodSystem α)

theorem trianglelefteq_iterSys : V ⊴ iterSys V :=
  trianglelefteq_of_projectionPair (embedIntoPow V) (head V)
    (head_comp_embedIntoPow V) (embedIntoPow_comp_head_le V)
end

set_option linter.unusedVariables false

theorem example_825_embed.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) :=
  @DomainTheory.NeighbourhoodSystems.trianglelefteq_iterSys

section
open NeighborhoodSystem
variable {α : Type*}

def arrowReindexOrderIso {ι ι' : Type*} (e : ι ≃ ι') (E : Type*) [Preorder E] :
    (ι → E) ≃o (ι' → E) where
  toFun f i' := f (e.symm i')
  invFun g i := g (e i)
  left_inv f := by funext i; simp
  right_inv g := by funext i'; simp
  map_rel_iff' := by
    intro f g
    constructor
    · intro h i
      simpa using h (e i)
    · intro h i'
      simpa using h (e.symm i')

def sumArrowOrderIso (α β : Type*) (E : Type*) [Preorder E] :
    (α ⊕ β → E) ≃o (α → E) × (β → E) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun p := Sum.elim p.1 p.2
  left_inv f := by funext i; cases i <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h1, h2⟩ i
      cases i with
      | inl a => exact h1 a
      | inr b => exact h2 b
    · intro h
      exact ⟨fun a => h (Sum.inl a), fun b => h (Sum.inr b)⟩

def interleaveOrderIso (E : Type*) [Preorder E] : (ℕ → E) × (ℕ → E) ≃o (ℕ → E) :=
  (sumArrowOrderIso ℕ ℕ E).symm.trans (arrowReindexOrderIso Equiv.natSumNatEquivNat E)

def powProdOrderIso (V : NeighborhoodSystem α) :
    (prod (iterSys V) (iterSys V)).Element ≃o (iterSys V).Element :=
  (prodEquiv (iterSys V) (iterSys V)).trans <|
    (prodCongrOrderIso (iterSeqEquiv V) (iterSeqEquiv V)).trans <|
      (interleaveOrderIso V.Element).trans (iterSeqEquiv V).symm

theorem pow_prod_isomorphic (V : NeighborhoodSystem α) :
    prod (iterSys V) (iterSys V) ≅ᴰ iterSys V :=
  ⟨powProdOrderIso V⟩

end

set_option linter.unusedVariables false

theorem example_825_pow.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum (Prod Nat α) (Prod Nat α)) (Prod Nat α)
    (@DomainTheory.NeighbourhoodSystems.prod (Prod Nat α) (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
      (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V) :=
  @DomainTheory.NeighbourhoodSystems.pow_prod_isomorphic

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*}

def isoOfUnique (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    [Unique V₀.Element] [Unique V₁.Element] : V₀.Element ≃o V₁.Element where
  toFun _ := default
  invFun _ := default
  left_inv x := (Unique.eq_default x).symm
  right_inv y := (Unique.eq_default y).symm
  map_rel_iff' := by
    intro a b
    exact iff_of_true (le_refl _) (le_of_eq (Subsingleton.elim a b))

instance uniqueApproximableMapUnitSys : Unique (ApproximableMap unitSys unitSys) where
  default := idMap unitSys
  uniq _f := ApproximableMap.ext_of_toElementMap fun _x => Subsingleton.elim _ _

instance uniqueFunSpaceUnitSys : Unique (funSpace unitSys unitSys).Element where
  default := (funSpaceEquiv unitSys unitSys).symm default
  uniq _x := (funSpaceEquiv unitSys unitSys).injective (Subsingleton.elim _ _)

theorem isomorphic_of_unique (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    [Unique V₀.Element] [Unique V₁.Element] : V₀ ≅ᴰ V₁ :=
  ⟨isoOfUnique V₀ V₁⟩

theorem funSpace_unitSys_isomorphic : funSpace unitSys unitSys ≅ᴰ unitSys :=
  isomorphic_of_unique _ _

end

set_option linter.unusedVariables false

theorem example_825_unit : @DomainTheory.NeighbourhoodSystems.Isomorphic
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Unit Unit DomainTheory.NeighbourhoodSystems.unitSys
    DomainTheory.NeighbourhoodSystems.unitSys)
  Unit
  (@DomainTheory.NeighbourhoodSystems.funSpace Unit Unit DomainTheory.NeighbourhoodSystems.unitSys
    DomainTheory.NeighbourhoodSystems.unitSys)
  DomainTheory.NeighbourhoodSystems.unitSys :=
  DomainTheory.NeighbourhoodSystems.funSpace_unitSys_isomorphic

open NeighborhoodSystem ApproximableMap

abbrev RDom := prod (funSpace U U) (prod (funSpace U U) U)

noncomputable def RMap (c : ApproximableMap U U) : ApproximableMap RDom U :=
  c.comp ((evalMap U U).comp
    (paired
      ((proj₀ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) (prod (funSpace U U) U))
          ((proj₁ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))))))

noncomputable def curryOnceC (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace (prod (funSpace U U) U) U) :=
  curry (RMap c)

noncomputable def fixedNbhd_elementIso_fix {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (fixedNbhd a).Element ≃o {y : U.Element // a.toElementMap y = y} := by
  have h := Subsystem.elementIso (fixedNbhd_subsystem a)
  unfold Subsystem.retractionOfSubsystem at h
  rwa [inj_comp_proj_eq_self ha] at h

noncomputable def lamOp (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace (funSpace U U) (funSpace U U)) :=
  (curryC (funSpace U U) U U).comp (curryOnceC c)

noncomputable def presentationIterU : ComputablePresentation (iterSys U) :=
  Classical.choice (iterSys_isEffectivelyGiven U_isEffectivelyGiven)

noncomputable def cInj : ApproximableMap (iterSys U) U :=
  (theorem_8_8_b_strong presentationIterU).choose

noncomputable def cProj : ApproximableMap U (iterSys U) :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose

noncomputable def cCombinator : ApproximableMap U U := cInj.comp cProj

noncomputable def TArrow (a : ApproximableMap U U) : Σ β : Type, NeighborhoodSystem β :=
  ⟨_, funSpace (fixedNbhd a) (fixedNbhd cCombinator)⟩

theorem cProj_comp_cInj : cProj.comp cInj = idMap (iterSys U) :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose_spec.1

noncomputable def cElementIso :
    (iterSys U).Element ≃o {y : U.Element // cCombinator.toElementMap y = y} :=
  elementIsoOfProjectionPair cInj cProj cProj_comp_cInj rfl

noncomputable def tOpMap (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  (expMap jArrow iArrow).comp (lamOp c)

theorem cInj_comp_cProj_le : cInj.comp cProj ≤ idMap U :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose_spec.2.1

theorem isFinitary_cCombinator : IsFinitary cCombinator :=
  isFinitary_of_projectionPair cInj cProj cProj_comp_cInj rfl

theorem isRetraction_cCombinator : Retraction cCombinator := by
  constructor
  show (cInj.comp cProj).comp (cInj.comp cProj) = cInj.comp cProj
  rw [comp_assoc, ← comp_assoc cProj cInj cProj, cProj_comp_cInj, idMap_comp]

theorem isProjection_cCombinator : IsProjection cCombinator :=
  ⟨isRetraction_cCombinator, cInj_comp_cProj_le⟩

theorem isFinitaryProjection_cCombinator : FinitaryProjection cCombinator :=
  ⟨⟨isProjection_cCombinator, isFinitary_cCombinator⟩⟩

theorem fixedNbhd_cCombinator_isomorphic : fixedNbhd cCombinator ≅ᴰ iterSys U :=
  ⟨(fixedNbhd_elementIso_fix isFinitaryProjection_cCombinator).trans cElementIso.symm⟩

theorem hVV_cCombinator :
    prod (fixedNbhd cCombinator) (fixedNbhd cCombinator) ≅ᴰ fixedNbhd cCombinator :=
  ((fixedNbhd_cCombinator_isomorphic.prod fixedNbhd_cCombinator_isomorphic).trans
    (pow_prod_isomorphic U)).trans fixedNbhd_cCombinator_isomorphic.symm

theorem toElementMap_RMap (c : ApproximableMap U U) (ψ φ : (funSpace U U).Element) (x : U.Element) :
    (RMap c).toElementMap (pair ψ (pair φ x)) =
      c.toElementMap ((toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x)) := by
  simp only [RMap, toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

theorem toApproxMap_lamOp (c a : ApproximableMap U U) :
    toApproxMap ((lamOp c).toElementMap (toFilter a)) = expMap a c := by
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ApproximableMap.ext_of_toElementMap
  intro x
  show (toApproxMap ((toApproxMap ((lamOp c).toElementMap (toFilter a))).toElementMap φ)).toElementMap x
    = (toApproxMap ((expMap a c).toElementMap φ)).toElementMap x
  rw [lamOp, toElementMap_comp, curryC_toApproxMap, toElementMap_curry_apply, curryOnceC,
    toElementMap_curry_apply, toElementMap_RMap, Sub8_6.toApproxMap_toFilter,
    expMap.toApproxMap_toElementMap, toElementMap_comp, toElementMap_comp]

theorem tOp_tOpMap (c a : ApproximableMap U U) :
    Exercise823.tOp (tOpMap c) a = arrowComb a c := by
  show toApproxMap ((tOpMap c).toElementMap (toFilter a)) = arrowComb a c
  rw [tOpMap, toElementMap_comp, expMap.toApproxMap_toElementMap, toApproxMap_lamOp,
    expMap.eq_lamComb]
  rfl

theorem hT_TArrow (a : ApproximableMap U U) (ha : FinitaryProjection a) :
    Nonempty (Exercise823.Fix (Exercise823.tOp (tOpMap cCombinator) a) ≃o
      (TArrow a).2.Element) := by
  rw [tOp_tOpMap]
  exact ⟨(arrowComb.elementIso a cCombinator ha isFinitaryProjection_cCombinator).symm⟩

theorem ht_tOpMap (c : ApproximableMap U U) (hc : FinitaryProjection c) :
    ∀ a, FinitaryProjection a → FinitaryProjection (Exercise823.tOp (tOpMap c) a) := by
  intro a ha
  rw [tOp_tOpMap]
  exact arrowComb.finitaryProjection a c ha hc

theorem Dsol_isomorphic_funSpace_cCombinator :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) (fixedNbhd cCombinator) := by
  have hht := ht_tOpMap cCombinator isFinitaryProjection_cCombinator
  have hFP := Exercise823.isFinitaryProjection_fixOp (tOpMap cCombinator) hht
  have h1 : Nonempty ((fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))).Element ≃o
      Exercise823.Fix (Exercise823.fixOp (tOpMap cCombinator))) :=
    ⟨fixedNbhd_elementIso_fix hFP⟩
  have h2 := Exercise823.fixedDomain_fixOp_iso_T (tOpMap cCombinator) hht TArrow hT_TArrow
  exact h1.elim fun e1 => h2.elim fun e2 => ⟨e1.trans e2⟩

theorem U_trianglelefteq_Dsol : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) := by
  set D := fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) with hD
  have h1 : U ⊴ iterSys U := trianglelefteq_iterSys U
  have h2 : iterSys U ⊴ fixedNbhd cCombinator :=
    ⟨fixedNbhd cCombinator, Subsystem.refl _, fixedNbhd_cCombinator_isomorphic.symm⟩
  have h3 : fixedNbhd cCombinator ⊴ funSpace D (fixedNbhd cCombinator) :=
    trianglelefteq_funSpace_const D (fixedNbhd cCombinator)
  have h4 : funSpace D (fixedNbhd cCombinator) ⊴ D :=
    ⟨D, Subsystem.refl D, Dsol_isomorphic_funSpace_cCombinator.symm⟩
  exact trianglelefteq_trans (trianglelefteq_trans (trianglelefteq_trans h1 h2) h3) h4

theorem exercise_8_25_main :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  funSpace_self_isomorphic Dsol_isomorphic_funSpace_cCombinator hVV_cCombinator

set_option linter.unusedVariables false

theorem example_825_fixed_point : @DomainTheory.NeighbourhoodSystems.Isomorphic Rat
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator))))
  (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
    (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
      (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))) :=
  DomainTheory.NeighbourhoodSystems.exercise_8_25_main

theorem exercise_8_25 :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  exercise_8_25_main

theorem exercise_8_25_universal : U ⊴ fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) :=
  U_trianglelefteq_Dsol

set_option linter.unusedVariables false

theorem example_825 : And
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Rat
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator))))
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq Rat Rat DomainTheory.NeighbourhoodSystems.U
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))) :=
  @And.intro
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Rat
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator))))
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq Rat Rat DomainTheory.NeighbourhoodSystems.U
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator))))
  DomainTheory.NeighbourhoodSystems.exercise_8_25 DomainTheory.NeighbourhoodSystems.exercise_8_25_universal

end DomainTheory.NeighbourhoodSystems
