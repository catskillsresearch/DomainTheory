module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subUFixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subUFixIsoSubFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.PolymorphicType
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDUncurried
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDApply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piUFixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.scFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.scPrincipal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDTypeMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDType
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.jArrow_comp_iArrow_apply
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subApprox_fix_of_subU_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU_fix_of_subApprox_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD_fix_of_piU_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piU_fix_of_piD_fix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.BasicInst38

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **Conjugating a retraction of `(𝒰→𝒰)` through `i_→, j_→` gives a retraction of `𝒰`.** Pure
associativity plus `j_→∘i_→ = I` (`jArrow_comp_iArrow`) and `H∘H=H`. -/
theorem isRetraction_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : Retraction H) : Retraction (iArrow.comp (H.comp jArrow)) := by
  constructor
  show (iArrow.comp (H.comp jArrow)).comp (iArrow.comp (H.comp jArrow)) =
    iArrow.comp (H.comp jArrow)
  rw [comp_assoc iArrow (H.comp jArrow) (iArrow.comp (H.comp jArrow)),
    comp_assoc H jArrow (iArrow.comp (H.comp jArrow)),
    ← comp_assoc jArrow iArrow (H.comp jArrow), jArrow_comp_iArrow, idMap_comp,
    ← comp_assoc H H jArrow, hH.out]

/-- **Conjugating a `≤ I`-map of `(𝒰→𝒰)` through `i_→, j_→` gives a `≤ I`-map of `𝒰`.** Chains
`comp_mono_gen` with `i_→∘j_→ ≤ I` (`iArrow_comp_jArrow_le`, Definition 8.9). -/
theorem le_idMap_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : H ≤ idMap (funSpace U U)) : iArrow.comp (H.comp jArrow) ≤ idMap U :=
  calc iArrow.comp (H.comp jArrow)
      ≤ iArrow.comp ((idMap (funSpace U U)).comp jArrow) :=
        comp_mono_gen le_rfl (comp_mono_gen hH le_rfl)
    _ = iArrow.comp jArrow := by rw [idMap_comp]
    _ ≤ idMap U := iArrow_comp_jArrow_le

/-- **Conjugating a projection of `(𝒰→𝒰)` through `i_→, j_→` gives a projection of `𝒰`.** -/
theorem isProjection_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : IsProjection H) : IsProjection (iArrow.comp (H.comp jArrow)) :=
  ⟨isRetraction_conjArrow hH.1, le_idMap_conjArrow hH.2⟩

/-- **`subU` is a projection.** -/
theorem isProjection_subU : IsProjection subU :=
  isProjection_conjArrow Sub8_6.isProjection_subApprox


/-- **`subU` is finitary.** Composes `subUFixIso` with Theorem 8.6(b)(ii)'s `isFinitary_subApprox`. -/
theorem isFinitary_subU : IsFinitary subU := by
  obtain ⟨β, F, ⟨iso⟩⟩ := Sub8_6.isFinitary_subApprox (E := U)
  exact ⟨β, F, ⟨subUFixIso.trans iso⟩⟩

/-- **`sub`, regarded as a combinator on `𝒰` itself, is a finitary projection** (Exercise 8.27's
opening sentence, in full). -/
theorem isFinitaryProjection_subU : FinitaryProjection subU :=
  ⟨⟨isProjection_subU, isFinitary_subU⟩⟩


/-- If `a` is idempotent and `f = a∘g∘a` for *some* `g`, then `a(f(z)) = f(z)` for *every* `z` —
i.e. any map "sandwiched" between two copies of an idempotent `a` always lands in `Fix(a)`,
regardless of what `g` is. (General form of the pattern behind Exercise 8.26's
`translateApp_hasType`, but derived automatically rather than assumed as a hypothesis.) -/
theorem toElementMap_mem_fix_of_isRetraction_sandwich {a g : ApproximableMap U U}
    (ha : Retraction a) (z : U.Element) :
    a.toElementMap ((a.comp (g.comp a)).toElementMap z) = (a.comp (g.comp a)).toElementMap z := by
  rw [toElementMap_comp, ← toElementMap_comp a a, ha.out]

/-- **The exercise's own justification, formalized**: "whenever `t` is a finitary projection, then
so is `d(t)`" — in fact, for `d` a polymorphic type, `d(z) ∈ Fix(subU)` for *every* `z`, not just
for `z` a "type". -/
theorem polymorphicType_apply_mem_fix {d : ApproximableMap U U} (hd : PolymorphicType d)
    (z : U.Element) : subU.toElementMap (d.toElementMap z) = d.toElementMap z := by
  have h := toElementMap_mem_fix_of_isRetraction_sandwich isProjection_subU.1 (g := d) z
  rwa [hd.out] at h

/-- **Any `j_→`-decoded fixed point of `subU` is a finitary projection of `𝒰`.** -/
theorem isFinitaryProjection_toApproxMap_jArrow_of_fix {w : U.Element}
    (hw : subU.toElementMap w = w) :
    FinitaryProjection (toApproxMap (jArrow.toElementMap w)) := by
  apply isFinitaryProjection_of_sub_eq_self
  have hfix := subApprox_fix_of_subU_fix hw
  have hstep := congrArg toApproxMap hfix
  rwa [Sub8_6.toElementMap_subApprox, Sub8_6.toApproxMap_subFilter] at hstep

/-- **The key lemma: `j_→(subU(z))` is always a finitary projection of `𝒰`, for any `z`.** -/
theorem isFinitaryProjection_decode_subU (z : U.Element) :
    FinitaryProjection (toApproxMap (jArrow.toElementMap (subU.toElementMap z))) :=
  isFinitaryProjection_toApproxMap_jArrow_of_fix
    (toElementMap_idem_of_isRetraction isProjection_subU.1 z)


theorem toElementMap_piDUncurried (d : ApproximableMap U U) (φ : (funSpace U U).Element)
    (t : U.Element) :
    (piDUncurried d).toElementMap (pair φ t) =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap
        ((toApproxMap φ).toElementMap (subU.toElementMap t)) := by
  simp only [piDUncurried, toElementMap_comp, toElementMap_paired, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]


theorem toElementMap_piDApply (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  simp only [piDApply, toElementMap_comp, toElementMap_paired, evalMap_apply]

/-- **`piD d`, transported through `funSpaceEquiv`, is exactly `piDApply d`.** Mirrors
`toApproxMap_toElementMap_lamComb`/`toApproxMap_toElementMap_expMap`. -/
theorem toApproxMap_toElementMap_piD (d : ApproximableMap U U) (φ : (funSpace U U).Element) :
    toApproxMap ((piD d).toElementMap φ) = piDApply d (toApproxMap φ) := by
  apply ApproximableMap.ext_of_toElementMap
  intro t
  rw [piD, toElementMap_curry_apply, toElementMap_piDUncurried, toElementMap_piDApply]


/-- **Exercise 8.27(b)(2)(a).** `(piD d).rel X W` reduces to a literal membership test — the direct
specialization of `curry_rel` (`FunctionSpace.lean`), no new proof needed. -/
theorem piD_rel_iff (d : ApproximableMap U U) {X W : Set (ApproximableMap U U)} :
    (piD d).rel X W ↔ ∃ hX : (funSpace U U).mem X, (funSpace U U).mem W ∧
      gSection (piDUncurried d) hX ∈ W :=
  curry_rel

/-- **Exercise 8.27(b)(2)(b).** `gSection (piDUncurried d) hX`'s own relation, fully unwound to a
closed elementwise formula in terms of the already-proven closed form `piDApply` (built, in its
own proof, purely from `subU`'s and `d`'s `toElementMap` actions plus `evalMap_apply`): reduce via
`gSection_rel` to `(piDUncurried d).rel (prodNbhd X Y) Z`, then via `rel_iff_mem_principal` +
`pair_principal_eq_principal_prodNbhd` to the element pair `pair (principal hX) (principal hY)`,
then read off `toElementMap_piDUncurried`/`toElementMap_piDApply`. This is the "unwind `piD d`'s
neighbourhood relation" content of Exercise 8.27(b)(2). -/
theorem gSection_piDUncurried_rel_iff (d : ApproximableMap U U)
    {X : Set (ApproximableMap U U)} (hX : (funSpace U U).mem X) {Y Z : Set ℚ} (hY : U.mem Y) :
    (gSection (piDUncurried d) hX).rel Y Z ↔
      ((piDApply d (toApproxMap ((funSpace U U).principal hX))).toElementMap
        (U.principal hY)).mem Z := by
  rw [gSection_rel, rel_iff_mem_principal (piDUncurried d) (prod_mem_prodNbhd hX hY),
    ← pair_principal_eq_principal_prodNbhd hX hY, toElementMap_piDUncurried,
    ← toElementMap_piDApply]

/-- **Exercise 8.27(b)(3)(a).** `hii`'s LHS, reduced to a literal membership test: no abstract
"funSpace element" reasoning left, purely `piDApply d (toApproxMap x) ∈ Y` as an actual map/set. -/
theorem piD_toElementMap_mem_iff (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ piDApply d (toApproxMap x) ∈ Y := by
  conv_lhs => rw [← Sub8_6.toFilter_toApproxMap ((piD d).toElementMap x)]
  rw [mem_toFilter, toApproxMap_toElementMap_piD]

/-- **Exercise 8.27(b)(3), the `⟸` half — closes unconditionally, for any `d` at all.** Direct
specialization of `Theorem85.lean`'s newly-extracted `mem_of_exists_rel_self` (no hypothesis on
`a` needed) to `a := piD d`. The remaining, genuinely hard direction is documented above and in
`HANDOFF.md`; **not** attempted here. -/
theorem hii_easy_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    {X : Set (ApproximableMap U U)} (hXx : x.mem X) (hXY : X ⊆ Y) (hXX : (piD d).rel X X) :
    ((piD d).toElementMap x).mem Y :=
  mem_of_exists_rel_self x hYE hXx hXY hXX

/-- **`subU`'s self-relating neighbourhoods are exactly fixed under `principal`.** If `subU.rel T T`,
the "witnessing element" `↑T` is *exactly* fixed by `subU` (not merely approximated): `≤` is
`subU`'s projection property (`subU ≤ I`), `≥` is `principal_le_of_mem` applied to the membership
`subU.rel T T` gives via `rel_iff_mem_principal`. -/
theorem subU_principal_eq_of_rel_self {T : Set ℚ} (hT : U.mem T) (hTT : subU.rel T T) :
    subU.toElementMap (U.principal hT) = U.principal hT := by
  apply le_antisymm
  · exact toElementMap_le_self_of_le_idMap isProjection_subU.2 _
  · exact principal_le_of_mem ((subU.rel_iff_mem_principal hT).mp hTT)

/-- **Descending to a self-consistent approximant.** For `t` already `subU`-fixed, formula (ii) for
`subU` (Exercise 8.27(a)) applied at `t` and any target `T₀ ∈ t` produces a *self-consistent*
`T ⊆ T₀` still in `t`'s filter — the cofinality fact that makes the self-consistent nbhds a directed
family sup-ing to `t` itself (`eq_iSupDirected_scPrincipal` below). -/
theorem exists_rel_self_subset_of_mem {t : U.Element} (ht : subU.toElementMap t = t)
    {T₀ : Set ℚ} (hT₀ : t.mem T₀) : ∃ T, subU.rel T T ∧ t.mem T ∧ T ⊆ T₀ := by
  have hmem : (subU.toElementMap t).mem T₀ := by rw [ht]; exact hT₀
  obtain ⟨_, T, hTt, hTT₀, hTT⟩ :=
    (formula_of_isFinitaryProjection isFinitaryProjection_subU t).mp hmem
  exact ⟨T, hTT, hTt, hTT₀⟩


/-- **`scFamily t`'s principals form a directed family.** Given `i, j`, apply
`exists_rel_self_subset_of_mem` at the common refinement `i.1 ∩ j.1` (valid via `t.inter_mem`). -/
theorem scFamily_directed {t : U.Element} (ht : subU.toElementMap t = t) :
    ∀ i j : scFamily t, ∃ k : scFamily t, scPrincipal i ≤ scPrincipal k ∧ scPrincipal j ≤ scPrincipal k :=
  fun i j => by
    obtain ⟨T, hTT, htT, hTsub⟩ := exists_rel_self_subset_of_mem ht (t.inter_mem i.2.2 j.2.2)
    refine ⟨⟨T, hTT, htT⟩, ?_, ?_⟩
    · exact (U.principal_le_iff (t.sub i.2.2) (t.sub htT)).mpr (hTsub.trans Set.inter_subset_left)
    · exact (U.principal_le_iff (t.sub j.2.2) (t.sub htT)).mpr (hTsub.trans Set.inter_subset_right)

/-- **`t` is the directed sup of its own self-consistent approximants.** Cofinality
(`exists_rel_self_subset_of_mem`) shows the self-consistent sub-family already has the same sup as
the full principal-approximant family (`eq_iSupDirected_principal`), namely `t` itself. -/
theorem eq_iSupDirected_scPrincipal {t : U.Element} (ht : subU.toElementMap t = t) :
    t = NeighborhoodSystem.iSupDirected scPrincipal (scFamily_directed ht) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ
    obtain ⟨T, hTT, htT, hTZ⟩ := exists_rel_self_subset_of_mem ht hZ
    exact ⟨⟨T, hTT, htT⟩, (U.mem_principal _).mpr ⟨t.sub hZ, hTZ⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨hZmem, hTZ⟩ := (U.mem_principal _).mp hi
    exact t.up_mem i.2.2 hZmem hTZ


end DomainTheory.NeighbourhoodSystems
