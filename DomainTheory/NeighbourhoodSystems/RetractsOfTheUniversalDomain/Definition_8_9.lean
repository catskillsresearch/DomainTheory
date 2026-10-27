module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Exercise326

/- concordance: source L5028 DEFINITION 8.9 constructs on projections -/
/-- **`i_→ : (𝒰→𝒰) → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰→𝒰`. -/
noncomputable def iArrow : ApproximableMap (funSpace U U) U :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose

/-- **`i₊ : 𝒰+𝒰 → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰+𝒰`. -/
noncomputable def iPlus : ApproximableMap (sum U U U_mem_nonempty U_mem_nonempty) U :=
  (theorem_8_8_b_strong sumUUPresentation).choose

/-- **`i_× : 𝒰×𝒰 → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰×𝒰`. -/
noncomputable def iTimes : ApproximableMap (prod U U) U :=
  (theorem_8_8_b_strong prodUUPresentation).choose

/-- **`j_→ : 𝒰 → (𝒰→𝒰)`** (Definition 8.9). -/
noncomputable def jArrow : ApproximableMap U (funSpace U U) :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose

/-- **`a → b : 𝒰 → 𝒰`** (Definition 8.9): `i_→ ∘ (λf. b∘f∘a) ∘ j_→`. -/
noncomputable def arrowComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((lamComb a b).comp jArrow)

/-- **`j₊ : 𝒰 → 𝒰+𝒰`** (Definition 8.9). -/
noncomputable def jPlus : ApproximableMap U (sum U U U_mem_nonempty U_mem_nonempty) :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose

/-- **`j_× : 𝒰 → 𝒰×𝒰`** (Definition 8.9). -/
noncomputable def jTimes : ApproximableMap U (prod U U) :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose

/-- **`a × b : 𝒰 → 𝒰`** (Definition 8.9): `i_× ∘ ⟨a∘proj₀, b∘proj₁⟩ ∘ j_×`. -/
noncomputable def prodComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iTimes.comp ((paired (a.comp (proj₀ U U)) (b.comp (proj₁ U U))).comp jTimes)

theorem iArrow_comp_jArrow_le : iArrow.comp jArrow ≤ idMap U :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.1

theorem iArrow_isComputableMap :
    ComputableMap funSpaceUUPresentation UComputablePresentation iArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.1

theorem iPlus_comp_jPlus_le : iPlus.comp jPlus ≤ idMap U :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.1

theorem iPlus_isComputableMap : ComputableMap sumUUPresentation UComputablePresentation iPlus :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.2.1

theorem iTimes_comp_jTimes_le : iTimes.comp jTimes ≤ idMap U :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.1

theorem iTimes_isComputableMap :
    ComputableMap prodUUPresentation UComputablePresentation iTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.1

theorem jArrow_comp_iArrow : jArrow.comp iArrow = idMap _ :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.1

theorem jArrow_isComputableMap :
    ComputableMap UComputablePresentation funSpaceUUPresentation jArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.2

theorem jPlus_comp_iPlus : jPlus.comp iPlus = idMap _ :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.1

theorem jPlus_isComputableMap : ComputableMap UComputablePresentation sumUUPresentation jPlus :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.2.2

theorem jTimes_comp_iTimes : jTimes.comp iTimes = idMap _ :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.1

theorem jTimes_isComputableMap :
    ComputableMap UComputablePresentation prodUUPresentation jTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.2


section
open NeighborhoodSystem ApproximableMap Exercise326
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

theorem arrowComb_eq (a b : ApproximableMap U U) :
    arrowComb a b = iArrow.comp ((lamComb a b).comp jArrow) := rfl

/-- The image of `in₀` always reaches the left copy (witnessed by `V₀.master`, since `v.master_mem`
always holds and `in₀`'s relation only needs `inj₀ X ⊆ inj₀ V₀.master`). -/
theorem inMap₀_toElementMap_reaches_left {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₀.Element) :
    ∃ X, V₀.mem X ∧ ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₀ X) := by
  refine ⟨V₀.master, V₀.master_mem, V₀.master, v.master_mem, V₀.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inl ⟨V₀.master, V₀.master_mem, rfl⟩)

/-- The image of `in₁` always reaches the right copy. -/
theorem inMap₁_toElementMap_reaches_right {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₁.Element) :
    ∃ Y, V₁.mem Y ∧ ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₁ Y) := by
  refine ⟨V₁.master, V₁.master_mem, V₁.master, v.master_mem, V₁.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inr ⟨V₁.master, V₁.master_mem, rfl⟩)

theorem lamComb_eq (a b : ApproximableMap U U) :
    lamComb a b = curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a))) := rfl

/-- No element of `𝒟₀+𝒟₁` reaches into both the left and the right copy (Exercise 3.18's
disjointness `inj₀_inter_inj₁`, plus `not_sum_mem_empty`). -/
theorem not_sum_reaches_both {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
    {w : (sum V₀ V₁ h₀ h₁).Element} (hL : ∃ X, V₀.mem X ∧ w.mem (inj₀ X))
    (hR : ∃ Y, V₁.mem Y ∧ w.mem (inj₁ Y)) : False := by
  obtain ⟨X, _, hX⟩ := hL
  obtain ⟨Y, _, hY⟩ := hR
  have h := w.inter_mem hX hY
  rw [inj₀_inter_inj₁] at h
  exact not_sum_mem_empty (w.sub h)

theorem prodComb_eq (a b : ApproximableMap U U) :
    prodComb a b = iTimes.comp ((prodMap a b).comp jTimes) := rfl

/-- **`lamComb a b`, transported through `funSpaceEquiv`, is exactly `λf. b∘f∘a`.** Chains
`toElementMap_curry_apply` (Theorem 3.12(i)), `toElementMap_prodMap_pair`/`toElementMap_idMap`,
and `evalMap_apply` (Theorem 3.11(i)). -/
theorem toApproxMap_toElementMap_lamComb (a b : ApproximableMap U U)
    (φ : (funSpace U U).Element) :
    toApproxMap ((lamComb a b).toElementMap φ) = b.comp ((toApproxMap φ).comp a) := by
  apply ext_of_toElementMap
  intro z
  rw [lamComb_eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

/-- **Proposition 8.10, `→`-case (the `lamComb` half), retraction.** -/
theorem isRetraction_lamComb {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (lamComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_lamComb a b ((lamComb a b).toElementMap φ),
    toApproxMap_toElementMap_lamComb a b φ,
    comp_assoc b ((toApproxMap φ).comp a) a,
    ← comp_assoc b b (((toApproxMap φ).comp a).comp a), hb.out,
    comp_assoc (toApproxMap φ) a a, ha.out]

/-- **Proposition 8.10, `→`-case (the `lamComb` half), projection.** -/
theorem le_idMap_lamComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    lamComb a b ≤ idMap (funSpace U U) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap, ← (funSpaceEquiv U U).le_iff_le, funSpaceEquiv_apply,
    funSpaceEquiv_apply, toApproxMap_toElementMap_lamComb]
  calc b.comp ((toApproxMap φ).comp a) ≤ (idMap U).comp ((toApproxMap φ).comp (idMap U)) :=
        comp_mono_gen hb (comp_mono_gen le_rfl ha)
    _ = toApproxMap φ := by rw [comp_idMap, idMap_comp]

theorem toElementMap_arrowComb (a b : ApproximableMap U U) (x : U.Element) :
    (arrowComb a b).toElementMap x =
      iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x)) := by
  rw [arrowComb_eq]
  simp only [toElementMap_comp]

/-- `a ∘ a = a` unwound at the element level: `a(a(x)) = a(x)` for every `x`. -/
theorem toElementMap_idem_of_isRetraction {a : ApproximableMap E E} (ha : Retraction a)
    (x : E.Element) : a.toElementMap (a.toElementMap x) = a.toElementMap x := by
  rw [← toElementMap_comp, ha.out]

/-- If `i ∘ j ≤ I_E`, then `i(j(x)) ≤ x` for every `x ∈ |E|`. -/
theorem toElementMap_le_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) (x : E.Element) : i.toElementMap (j.toElementMap x) ≤ x := by
  have h := (le_iff_toElementMap_le.mp hij) x
  rwa [toElementMap_comp, toElementMap_idMap] at h

/-- `a ≤ idMap E` unwound at the element level: `a(x) ≤ x` for every `x`. -/
theorem toElementMap_le_self_of_le_idMap {a : ApproximableMap E E} (ha : a ≤ idMap E)
    (x : E.Element) : a.toElementMap x ≤ x := by
  have h := (le_iff_toElementMap_le.mp ha) x
  rwa [toElementMap_idMap] at h

/-- **Proposition 8.10, `→`-case, projection half.** -/
theorem le_idMap_arrowComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    arrowComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_arrowComb, toElementMap_idMap]
  calc iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x))
      ≤ iArrow.toElementMap (jArrow.toElementMap x) :=
        iArrow.toElementMap_mono
          (toElementMap_le_self_of_le_idMap (le_idMap_lamComb ha hb) _)
    _ ≤ x := toElementMap_le_of_comp_le_idMap iArrow_comp_jArrow_le x

/-- If `j ∘ i = I_D`, then `j(i(v)) = v` for every `v ∈ |D|`. -/
theorem toElementMap_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) (v : D.Element) : j.toElementMap (i.toElementMap v) = v := by
  rw [← toElementMap_comp, hji, toElementMap_idMap]

/-- **Proposition 8.10, `→`-case, retraction half.** -/
theorem isRetraction_arrowComb {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (arrowComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_arrowComb a b ((arrowComb a b).toElementMap x),
    toElementMap_arrowComb a b x, toElementMap_of_comp_eq_idMap jArrow_comp_iArrow,
    toElementMap_idem_of_isRetraction (isRetraction_lamComb ha hb)]

end
end DomainTheory.NeighbourhoodSystems
