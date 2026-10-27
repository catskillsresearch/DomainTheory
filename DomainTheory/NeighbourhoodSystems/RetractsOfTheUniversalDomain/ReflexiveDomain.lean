module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbedIntoPow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ExampleC_le_B
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp
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
/- concordance: source L5224 EXERCISE 8.25 reflexive function space -/
/-- **Exercise 8.25 (Scott 1981, PRG-19): `𝒟 ⊴ 𝒟^∞`**, for every `𝒟`. Specialized to `𝒟 = 𝒰` this is
Scott's remark `𝒰 ⊴ 𝒰^∞`. -/
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

/-- Reindexing a non-dependent `ι → E` arrow type along a bijection of index types is an order
isomorphism, for the pointwise order on both sides. (Named distinctly from `Exercise324Iter.lean`'s
`piCongrOrderIso`, which reindexes *dependent* `Pi` types along a fixed index type instead.) -/
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

/-- The pointwise order on `α ⊕ β → E` corresponds, coordinatewise, to the product order on
`(α → E) × (β → E)`: splitting a sum-indexed family into its two summand-indexed restrictions is an
order isomorphism. -/
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

/-- **Interleaving.** Two `ℕ`-indexed sequences of `E` can be merged, order-isomorphically, into a
single `ℕ`-indexed sequence, via the pairing bijection `ℕ ⊕ ℕ ≃ ℕ`. -/
def interleaveOrderIso (E : Type*) [Preorder E] : (ℕ → E) × (ℕ → E) ≃o (ℕ → E) :=
  (sumArrowOrderIso ℕ ℕ E).symm.trans (arrowReindexOrderIso Equiv.natSumNatEquivNat E)

/-- The order isomorphism `|𝒟^∞ × 𝒟^∞| ≃o |𝒟^∞|` underlying `pow_prod_isomorphic`. -/
def powProdOrderIso (V : NeighborhoodSystem α) :
    (prod (iterSys V) (iterSys V)).Element ≃o (iterSys V).Element :=
  (prodEquiv (iterSys V) (iterSys V)).trans <|
    (prodCongrOrderIso (iterSeqEquiv V) (iterSeqEquiv V)).trans <|
      (interleaveOrderIso V.Element).trans (iterSeqEquiv V).symm

/-- **Exercise 8.25 (Scott 1981, PRG-19), first step: `𝒟^∞ × 𝒟^∞ ≅ 𝒟^∞`**, for any `𝒟`. Specialized
to `𝒟 = 𝒰` this is Scott's `𝒰^∞ × 𝒰^∞ ≅ 𝒰^∞`. -/
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

/-- **Any two `NeighborhoodSystem`s with `Unique` element posets are isomorphic.** Both sides are
order-isomorphic to the one-point poset `PUnit`, so the isomorphism is forced. -/
def isoOfUnique (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    [Unique V₀.Element] [Unique V₁.Element] : V₀.Element ≃o V₁.Element where
  toFun _ := default
  invFun _ := default
  left_inv x := (Unique.eq_default x).symm
  right_inv y := (Unique.eq_default y).symm
  map_rel_iff' := by
    intro a b
    exact iff_of_true (le_refl _) (le_of_eq (Subsingleton.elim a b))

/-- **There is only one approximable self-map of `𝟙`, the identity.** Both maps induce the same
(unique) elementwise function, so `ext_of_toElementMap` identifies them. -/
instance uniqueApproximableMapUnitSys : Unique (ApproximableMap unitSys unitSys) where
  default := idMap unitSys
  uniq _f := ApproximableMap.ext_of_toElementMap fun _x => Subsingleton.elim _ _

/-- **`(𝟙 → 𝟙)` has a unique element**, transported from the unique approximable self-map of `𝟙`
along `funSpaceEquiv`. -/
instance uniqueFunSpaceUnitSys : Unique (funSpace unitSys unitSys).Element where
  default := (funSpaceEquiv unitSys unitSys).symm default
  uniq _x := (funSpaceEquiv unitSys unitSys).injective (Subsingleton.elim _ _)

/-- **Any two `NeighborhoodSystem`s with `Unique` element posets determine isomorphic domains.** -/
theorem isomorphic_of_unique (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    [Unique V₀.Element] [Unique V₁.Element] : V₀ ≅ᴰ V₁ :=
  ⟨isoOfUnique V₀ V₁⟩

/-- **Exercise 8.25 (Scott 1981, PRG-19) — the obstruction `𝟙 → 𝟙 = 𝟙`.** The terminal one-point
domain is a fixed point of `→`, carrying no information: this is why "the obvious solution by
retracts is of no use". -/
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

/-- The domain `(𝒰→𝒰) × ((𝒰→𝒰) × 𝒰)` of the joint evaluator: an element `⟨ψ, ⟨φ, x⟩⟩` packages
the varying map `ψ` (to become `a`), the curry variable `φ`, and the point `x`. -/
abbrev RDom := prod (funSpace U U) (prod (funSpace U U) U)

/-- `R(ψ, φ, x) := c(φ(ψ(x)))`, purely as a composite of `evalMap`, `proj`s and `paired` — jointly
continuous in `(ψ, φ, x)` since `evalMap` is. -/
noncomputable def RMap (c : ApproximableMap U U) : ApproximableMap RDom U :=
  c.comp ((evalMap U U).comp
    (paired
      ((proj₀ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) (prod (funSpace U U) U))
          ((proj₁ (funSpace U U) U).comp (proj₁ (funSpace U U) (prod (funSpace U U) U)))))))

/-- First curry (peeling off `ψ`), leaving the `(φ, x)` pair bundled: an element of
`𝒰→𝒰 → funSpace ((𝒰→𝒰) × 𝒰) 𝒰`. -/
noncomputable def curryOnceC (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace (prod (funSpace U U) U) U) :=
  curry (RMap c)

/-- **`fixedNbhd a ≅ Fix(a)`, for any finitary projection `a : 𝒰 → 𝒰`.** Theorem 8.6(a)'s
`inj_comp_proj_eq_self` identifies `retractionOfSubsystem (fixedNbhd_subsystem a)` with `a` itself,
transporting Proposition 8.2's `elementIso` along the identification. -/
noncomputable def fixedNbhd_elementIso_fix {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (fixedNbhd a).Element ≃o {y : U.Element // a.toElementMap y = y} := by
  have h := Subsystem.elementIso (fixedNbhd_subsystem a)
  unfold Subsystem.retractionOfSubsystem at h
  rwa [inj_comp_proj_eq_self ha] at h

/-- Second curry (via Table 5.5's `curryC`, peeling off `φ`): `ψ ↦ (φ ↦ (x ↦ R(ψ,φ,x)))`, an
element of the fourth-order function space `(𝒰→𝒰) → ((𝒰→𝒰) → (𝒰→𝒰))`. -/
noncomputable def lamOp (c : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace (funSpace U U) (funSpace U U)) :=
  (curryC (funSpace U U) U U).comp (curryOnceC c)

/-- A fixed computable presentation of `𝒰^∞ = iterSys 𝒰` (Exercise 7.15). -/
noncomputable def presentationIterU : ComputablePresentation (iterSys U) :=
  Classical.choice (iterSys_isEffectivelyGiven U_isEffectivelyGiven)

/-- **`i : 𝒰^∞ → 𝒰`**, fixed by Theorem 8.8(b) applied to `𝒰^∞`. -/
noncomputable def cInj : ApproximableMap (iterSys U) U :=
  (theorem_8_8_b_strong presentationIterU).choose

/-- **`j : 𝒰 → 𝒰^∞`**, fixed by Theorem 8.8(b) applied to `𝒰^∞`. -/
noncomputable def cProj : ApproximableMap U (iterSys U) :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose

/-- **`c := i ∘ j : 𝒰 → 𝒰`**, the finitary projection witnessing `𝒰^∞` inside `𝒰`. -/
noncomputable def cCombinator : ApproximableMap U U := cInj.comp cProj

/-- Exercise 8.23's abstract correspondence `T(a) := D_a → D_c` (a domain, for each finitary
projection `a`). -/
noncomputable def TArrow (a : ApproximableMap U U) : Σ β : Type, NeighborhoodSystem β :=
  ⟨_, funSpace (fixedNbhd a) (fixedNbhd cCombinator)⟩

theorem cProj_comp_cInj : cProj.comp cInj = idMap (iterSys U) :=
  (theorem_8_8_b_strong presentationIterU).choose_spec.choose_spec.1

/-- **`𝒰^∞ ≅ Fix(c)`**, from the generic projection-pair `elementIso` (Proposition 8.10(b)'s
`elementIsoOfProjectionPair`). -/
noncomputable def cElementIso :
    (iterSys U).Element ≃o {y : U.Element // cCombinator.toElementMap y = y} :=
  elementIsoOfProjectionPair cInj cProj cProj_comp_cInj rfl

/-- **`t(a) := a → c`, made continuous in `a`.** Conjugates `lamOp c`'s output by the fixed
projection pair `jArrow : 𝒰 → (𝒰→𝒰)`, `iArrow : (𝒰→𝒰) → 𝒰` (Definition 8.9), via `expMap jArrow
iArrow`. -/
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

/-- **`fixedNbhd c ≅ 𝒰^∞`.** -/
theorem fixedNbhd_cCombinator_isomorphic : fixedNbhd cCombinator ≅ᴰ iterSys U :=
  ⟨(fixedNbhd_elementIso_fix isFinitaryProjection_cCombinator).trans cElementIso.symm⟩

/-- **`fixedNbhd c × fixedNbhd c ≅ fixedNbhd c`**, transported from `Exercise825Pow.pow_prod_isomorphic`
along `fixedNbhd_cCombinator_isomorphic`. -/
theorem hVV_cCombinator :
    prod (fixedNbhd cCombinator) (fixedNbhd cCombinator) ≅ᴰ fixedNbhd cCombinator :=
  ((fixedNbhd_cCombinator_isomorphic.prod fixedNbhd_cCombinator_isomorphic).trans
    (pow_prod_isomorphic U)).trans fixedNbhd_cCombinator_isomorphic.symm

theorem toElementMap_RMap (c : ApproximableMap U U) (ψ φ : (funSpace U U).Element) (x : U.Element) :
    (RMap c).toElementMap (pair ψ (pair φ x)) =
      c.toElementMap ((toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x)) := by
  simp only [RMap, toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-- **`lamOp c` recovers `expMap (-) c = lamComb (-) c` at every `a`.** The heart of the
continuity argument: unwinding both curry layers (`curryC_toApproxMap`, `toElementMap_curry_apply`
twice) and `RMap`'s value formula (`toElementMap_RMap`) against `expMap`'s own value formula
(`expMap.toApproxMap_toElementMap`) shows both sides send `φ` to (the element representing)
`x ↦ c(φ(a(x)))`. -/
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

/-- **`tOp (tOpMap c) a = arrowComb a c`**, for every `a`: `t` really does implement
`a ↦ arrowComb a c`, continuously. -/
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

/-- **`t` sends finitary projections to finitary projections** (Exercise 8.23's hypothesis `ht`),
via `tOp_tOpMap` and Proposition 8.10(b)'s `arrowComb.finitaryProjection`. -/
theorem ht_tOpMap (c : ApproximableMap U U) (hc : FinitaryProjection c) :
    ∀ a, FinitaryProjection a → FinitaryProjection (Exercise823.tOp (tOpMap c) a) := by
  intro a ha
  rw [tOp_tOpMap]
  exact arrowComb.finitaryProjection a c ha hc

/-- **`D ≅ D → 𝒰^∞` for `D := fixedNbhd (fixOp t)`.** Exercise 8.23's `fixedDomain_fixOp_iso_T`
gives `Fix(‖t‖) ≅ D → D_c`; `fixedNbhd_elementIso_fix` identifies `D`'s own element type with
`Fix(‖t‖)`, and `fixedNbhd_cCombinator_isomorphic` identifies `D_c` with `𝒰^∞`. -/
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

/-- **`𝒰 ⊴ D`**: the solution domain contains a copy of the universal domain `𝒰`, so it is
non-trivial (Scott's remark). Chains `𝒰 ⊴ 𝒰^∞` (`Exercise825Embed.trianglelefteq_iterSys`),
`𝒰^∞ ≅ fixedNbhd c`, the general constant-function embedding `𝒱 ⊴ (𝒟 → 𝒱)`
(`Exercise820.trianglelefteq_funSpace_const`), and `D → (fixedNbhd c) ≅ D`. -/
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

/-- **Exercise 8.25 (Scott 1981, PRG-19), main theorem.** `D ≅ D → D`, for
`D := fixedNbhd (fixOp (tOpMap cCombinator))`: a non-trivial domain isomorphic to its own function
space (see `U_trianglelefteq_Dsol` below for non-triviality). -/
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

/-- **Exercise 8.25 (Scott 1981, PRG-19), the answer.** The concrete domain
`D := fixedNbhd (fixOp (tOpMap cCombinator))` (built in `Exercise825FixedPoint.lean` by the
fixed-point method of Exercise 8.23, applied to `T(a) := a → 𝒰^∞`) satisfies `D ≅ D → D`. -/
theorem exercise_8_25 :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  exercise_8_25_main

/-- **Exercise 8.25 (Scott 1981, PRG-19), non-triviality/universality.** The solution domain `D`
of `exercise_8_25` contains a genuine embedded copy of the universal domain `𝒰` (`𝒰 ⊴ D`), so it is
certainly not the one-point domain, and is in fact universal: every countable neighbourhood system
embeds (up to isomorphism) into `𝒰`, hence into `D`. -/
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
