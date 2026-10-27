module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

namespace aSharp

/-- **`a ≤ I ⟹ a§ ≤ I`** (half of "`a` a projection ⟹ `a§` a projection", Proposition 8.10's
proof recipe transcribed to `§`). -/
theorem le_idMap_of_le {a : ApproximableMap U U} (ha : a ≤ idMap U) :
    aSharp a ≤ idMap U := by
  have h1 : (inSharpMap U_mem_nonempty).comp a ≤ inSharpMap U_mem_nonempty := by
    calc (inSharpMap U_mem_nonempty).comp a
        ≤ (inSharpMap U_mem_nonempty).comp (idMap U) := comp_mono_gen le_rfl ha
      _ = inSharpMap U_mem_nonempty := comp_idMap _
  have h2 : aSharpInner a ≤ idMap (Dsharp U U_mem_nonempty) := by
    calc aSharpInner a
        ≤ gMap (inSharpMap U_mem_nonempty) (pairSharpMap U_mem_nonempty) U_mem_nonempty :=
          gMap_mono U_mem_nonempty h1 le_rfl
      _ = idMap (Dsharp U U_mem_nonempty) := gMap_inSharp_pairSharp_eq_idMap
  calc aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := eq a
    _ ≤ iSharp.comp ((idMap (Dsharp U U_mem_nonempty)).comp jSharp) :=
        comp_mono_gen le_rfl (comp_mono_gen h2 le_rfl)
    _ = iSharp.comp jSharp := by rw [idMap_comp]
    _ ≤ idMap U := iSharp_comp_jSharp_le

/-- **`a§` is finitary whenever `a` is a finitary projection.** -/
theorem isFinitary {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    IsFinitary (aSharp a) :=
  isFinitary_of_projectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

/-- **`a§` is computable whenever `a` is.** -/
theorem isComputable {a : ApproximableMap U U}
    (ha : ComputableMap UComputablePresentation UComputablePresentation a) :
    ComputableMap UComputablePresentation UComputablePresentation (aSharp a) := by
  have hu : ComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty)
      ((inSharpMap U_mem_nonempty).comp a) :=
    comp_isComputable ha (inSharp_isComputable U_mem_nonempty UComputablePresentation)
  have hInner : ComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      (dsharpPresentation UComputablePresentation U_mem_nonempty) (aSharpInner a) :=
    gMap_isComputable U_mem_nonempty UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) hu
      (pairSharp_isComputable U_mem_nonempty UComputablePresentation)
  exact comp_isComputable (comp_isComputable jSharp_isComputableMap hInner) iSharp_isComputableMap

end aSharp


/-- **`a§`, unfolded one step through the `U§ ⊴ U` projection pair.** Mirrors
`Proposition810.lean`'s `toElementMap_prodComb`/`toElementMap_arrowComb` pattern. -/
theorem toElementMap_aSharp (a : ApproximableMap U U) (x : U.Element) :
    (aSharp a).toElementMap x
      = iSharp.toElementMap ((aSharpInner a).toElementMap (jSharp.toElementMap x)) := by
  rw [aSharp.eq]
  simp only [toElementMap_comp]

/-- **Exercise 8.21(b)(3).** Idempotence of `aSharpInner a` transports through the projection pair
`iSharp`/`jSharp` to idempotence of `aSharp a` itself — exactly `Proposition810.lean`'s
`isRetraction_prodComb`/`isRetraction_arrowComb` recipe (`toElementMap_of_comp_eq_idMap` +
`toElementMap_idem_of_isRetraction`), conjugated through `jSharp_comp_iSharp` instead of
`jTimes_comp_iTimes`/`jArrow_comp_iArrow`. -/
theorem isRetraction_aSharp {a : ApproximableMap U U} (ha2 : Retraction (aSharpInner a)) :
    Retraction (aSharp a) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_aSharp a ((aSharp a).toElementMap x),
    toElementMap_aSharp a x, toElementMap_of_comp_eq_idMap jSharp_comp_iSharp,
    toElementMap_idem_of_isRetraction ha2]

/-- **Exercise 8.21(b), assembled.** `a` a projection of `U` `⟹` `a§` a projection: the `≤ I` half
is 8.21(a)'s `aSharp.le_idMap_of_le`; the retraction half chains `aSharpInner_idem_of_isRetraction`
(the `gMap`-level idempotence, via the catamorphism-uniqueness lemma `gMap_eq_of_satisfies`) with
`isRetraction_aSharp` (transport through `U§ ⊴ U`). This completes "`a` a projection ⟹ `a§` a
projection" in full, matching `Proposition810.lean`'s `isProjection_sumComb`/`isProjection_prodComb`/
`isProjection_arrowComb`. -/
theorem isProjection_aSharp {a : ApproximableMap U U} (ha : IsProjection a) :
    IsProjection (aSharp a) :=
  ⟨isRetraction_aSharp (aSharpInner_idem_of_isRetraction ha.1), aSharp.le_idMap_of_le ha.2⟩

/-- **Exercise 8.21, in full (Scott 1981, PRG-19).** `a` a finitary projection of `U` `⟹` `a§` is
a finitary projection of `U`, with `D_{a§} ≅ (D_a)§`. -/
theorem isFinitaryProjection_aSharp {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    FinitaryProjection (aSharp a) :=
  ⟨⟨isProjection_aSharp ha.out.1, aSharp.isFinitary ha⟩⟩


/- Ex 8.25 closing / funSpace congruence -/
variable {γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {V : NeighborhoodSystem β}

theorem ofIso_comp_ofIso_symm (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e).comp (ofIso e.symm) = idMap V₀' := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

theorem funSpaceCongr_hij (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0.symm) (ofIso e1)).comp (expMap (ofIso e0) (ofIso e1.symm)) =
      idMap (funSpace V₀' V₁') := by
  rw [← expMap.comp, ofIso_comp_ofIso_symm, ofIso_comp_ofIso_symm, expMap.id]

theorem ofIso_symm_comp_ofIso (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e.symm).comp (ofIso e) = idMap V₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.symm_apply_apply]

theorem funSpaceCongr_hji (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0) (ofIso e1.symm)).comp (expMap (ofIso e0.symm) (ofIso e1)) =
      idMap (funSpace V₀ V₁) := by
  rw [← expMap.comp, ofIso_symm_comp_ofIso, ofIso_symm_comp_ofIso, expMap.id]

/-- **Two approximable maps that are *exact* (not merely `≤`) mutual inverses give an
order-isomorphism of element types.** The generic upgrade behind `elementIsoOfProjectionPair`
(`Proposition810b.lean`) when the projection-pair equation holds in *both* directions: then the
fixed-point subtype on the codomain side is *everything*, collapsing to a genuine bijection. -/
def orderIsoOfMutualInverse {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) (hij : i.comp j = idMap E) : D.Element ≃o E.Element where
  toFun := i.toElementMap
  invFun := j.toElementMap
  left_inv x := by rw [← toElementMap_comp, hji, toElementMap_idMap]
  right_inv y := by rw [← toElementMap_comp, hij, toElementMap_idMap]
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro h
      have hm := j.toElementMap_mono h
      rwa [← toElementMap_comp, ← toElementMap_comp, hji, toElementMap_idMap,
        toElementMap_idMap] at hm
    · intro h
      exact i.toElementMap_mono h

/-- **`funSpace` is a congruence for `≃o`.** `𝒟₀ ≃o 𝒟₀'`, `𝒟₁ ≃o 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≃o (𝒟₀' → 𝒟₁')`. -/
noncomputable def funSpaceCongrOrderIso (e0 : V₀.Element ≃o V₀'.Element)
    (e1 : V₁.Element ≃o V₁'.Element) :
    (funSpace V₀ V₁).Element ≃o (funSpace V₀' V₁').Element :=
  orderIsoOfMutualInverse (expMap (ofIso e0.symm) (ofIso e1)) (expMap (ofIso e0) (ofIso e1.symm))
    (funSpaceCongr_hji e0 e1) (funSpaceCongr_hij e0 e1)

/-- **Currying (Theorem 3.12), as a domain isomorphism.** `(𝒟₀ × 𝒟₁ → 𝒟₂) ≅ (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
theorem curry_isomorphic (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    funSpace (prod V₀ V₁) V₂ ≅ᴰ funSpace V₀ (funSpace V₁ V₂) :=
  ⟨curryIso V₀ V₁ V₂⟩


/-- **`funSpace` is a congruence for `≅ᴰ`.** `𝒟₀ ≅ᴰ 𝒟₀'`, `𝒟₁ ≅ᴰ 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁')`. -/
theorem funSpace_congr (h0 : V₀ ≅ᴰ V₀') (h1 : V₁ ≅ᴰ V₁') :
    funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁' :=
  h0.elim fun e0 => h1.elim fun e1 => ⟨funSpaceCongrOrderIso e0 e1⟩

/-- **`funSpace` congruence, domain slot.** `𝒟₀ ≅ᴰ 𝒟₀'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁)`. -/
theorem funSpace_congr_left (h0 : V₀ ≅ᴰ V₀') : funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁ :=
  funSpace_congr h0 (Isomorphic.refl V₁)

/-- **`funSpace` congruence, codomain slot.** `𝒟₁ ≅ᴰ 𝒟₁'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀ → 𝒟₁')`. -/
theorem funSpace_congr_right (h1 : V₁ ≅ᴰ V₁') : funSpace V₀ V₁ ≅ᴰ funSpace V₀ V₁' :=
  funSpace_congr (Isomorphic.refl V₀) h1


/-- **Closing argument, step 1.** `D ≅ D → V` and `V × V ≅ V` imply `D × D ≅ D`. -/
theorem prod_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    prod D D ≅ᴰ D :=
  ((hDV.prod hDV).trans (funProd_isomorphic).symm).trans
    ((funSpace_congr_right hVV).trans hDV.symm)

/-- **Closing argument, step 2 (Exercise 8.25's main equation).** `D ≅ D → V` and `V × V ≅ V`
imply `D ≅ D → D`. -/
theorem funSpace_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    D ≅ᴰ funSpace D D :=
  have hDD : prod D D ≅ᴰ D := prod_self_isomorphic hDV hVV
  have step : funSpace D D ≅ᴰ D :=
    ((funSpace_congr_right hDV).trans (curry_isomorphic D D V).symm).trans
      ((funSpace_congr_left hDD).trans hDV.symm)
  step.symm




end DomainTheory.NeighbourhoodSystems
