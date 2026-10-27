module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_21
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

public import Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_12

@[expose] public section

section
/- concordance: source L5267 EXERCISE 8.27 infinite cartesian products -/
-- Exercise827/jArrow_comp_iArrow_apply.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

theorem jArrow_comp_iArrow_apply (v : (funSpace U U).Element) :
    jArrow.toElementMap (iArrow.toElementMap v) = v := by
  rw [show jArrow.toElementMap (iArrow.toElementMap v) = (jArrow.comp iArrow).toElementMap v from
    (toElementMap_comp jArrow iArrow v).symm, jArrow_comp_iArrow, toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
/-- **`sub`, regarded as a finitary projection of `𝒰` itself** (the exercise's opening sentence):
conjugate Theorem 8.6(b)'s `subApprox : (𝒰→𝒰)→(𝒰→𝒰)` through the fixed pair `i_→, j_→`
(Definition 8.9), exactly as `a→b` is built from `λf.b∘f∘a` in `Definition89.lean`. -/
noncomputable def subU : ApproximableMap U U :=
  iArrow.comp (Sub8_6.subApprox.comp jArrow)
end

section
/-- **A polymorphic type** (Scott 1981, PRG-19, Exercise 8.27): `d = sub∘d∘sub`, `sub` here being
`subU` (Step 1's "`sub` regarded as a combinator on `𝒰`"). -/
class PolymorphicType (d : ApproximableMap U U) : Prop where
  out : subU.comp (d.comp subU) = d
end

section
/-- **`Π(d)(x)`, for `x` a plain map `𝒰 → 𝒰`** (not yet an element of the function space) — the
formula's "closed form" as a composite `ApproximableMap`, matching Scott's
`λt. sub(d(sub(t)))(x(sub(t)))` literally. -/
noncomputable def piDApply (d f : ApproximableMap U U) : ApproximableMap U U :=
  (evalMap U U).comp (paired (jArrow.comp (subU.comp (d.comp subU))) (f.comp subU))
end

section
/-- **`Π(d)(x)(t)`, uncurried**: an `ApproximableMap ((𝒰→𝒰) × 𝒰) 𝒰`, jointly continuous in
`(x, t)` for `d` fixed. -/
noncomputable def piDUncurried (d : ApproximableMap U U) : ApproximableMap (prod (funSpace U U) U) U :=
  (evalMap U U).comp
    (paired
      (jArrow.comp (subU.comp (d.comp (subU.comp (proj₁ (funSpace U U) U)))))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) U) (subU.comp (proj₁ (funSpace U U) U)))))
end

section
/-- **`Π(d)`, as a self-map of `(𝒰→𝒰)`** (currying `piDUncurried d` in `x`, leaving `t` bound). -/
noncomputable def piD (d : ApproximableMap U U) : ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (piDUncurried d)
end

section
/-- **`Π(d)`, regarded as a combinator living in `𝒰` itself** — conjugating `piD d` through
`i_→, j_→` (Definition 8.9), exactly as `subU` was built from `subApprox` in Step 1. This is what
Scott's "type" means: a self-map *of `𝒰`*, not of `(𝒰→𝒰)`. -/
noncomputable def piU (d : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((piD d).comp jArrow)
end

section
/-- The family of `subU`-self-consistent nbhds already in `t`'s filter. -/
def scFamily (t : U.Element) : Type := {T : Set ℚ // subU.rel T T ∧ t.mem T}
end

section
instance instNonemptyScFamily (t : U.Element) : Nonempty (scFamily t) :=
  ⟨⟨U.master, subU.master_rel, t.master_mem⟩⟩
end

section
/-- **The "type at `s`" map**, `decode(subU(d(s)))`, as a function of the *element* `s` (not just
`s = subU(principal Y)` for some `Y`). Packaging `piDApply`'s inner formula this way is what lets
continuity/monotonicity in `s` be stated directly. -/
noncomputable def piDTypeMap (d : ApproximableMap U U) : ApproximableMap U (funSpace U U) :=
  jArrow.comp (subU.comp d)
end

section
/-- The "type at `s`" itself, as an `ApproximableMap U U`. Always a finitary projection
(`isFinitaryProjection_piDType`, Step 4), for *any* `d` and `s`. -/
noncomputable def piDType (d : ApproximableMap U U) (s : U.Element) : ApproximableMap U U :=
  toApproxMap ((piDTypeMap d).toElementMap s)
end

section
/-- The principal element witnessed by a member of `scFamily t`. -/
def scPrincipal {t : U.Element} (i : scFamily t) : U.Element :=
  U.principal (t.sub i.2.2)
end

section
/-- `piU d`'s defining formula unfolded at the element level (mirrors `toElementMap_subU`). -/
theorem toElementMap_piU (d : ApproximableMap U U) (w : U.Element) :
    (piU d).toElementMap w =
      iArrow.toElementMap ((piD d).toElementMap (jArrow.toElementMap w)) := by
  unfold piU
  rw [toElementMap_comp, toElementMap_comp]
end

section
/-- Unfolds `(piU d).toElementMap w = w` into the statement that `j_→(w)` is already a fixed
point of `piD d` (mirrors `subApprox_fix_of_subU_fix`). -/
theorem piD_fix_of_piU_fix {d : ApproximableMap U U} {w : U.Element}
    (hw : (piU d).toElementMap w = w) :
    (piD d).toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_piU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep
end

section
/-- Mirrors `subU_fix_of_subApprox_fix`. -/
theorem piU_fix_of_piD_fix {d : ApproximableMap U U} {φ : (funSpace U U).Element}
    (hφ : (piD d).toElementMap φ = φ) :
    (piU d).toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_piU, jArrow_comp_iArrow_apply, hφ]
end

section
/-- **Exercise 8.27(b)(0): `Fix(piU d) ≃o Fix(piD d)`.** Forward: `w ↦ j_→(w)`; backward:
`φ ↦ i_→(φ)`. Needs only `j_→∘i_→ = I` (no inequality on `i_→∘j_→`) — mirrors `subUFixIso`
verbatim, with `piD d`/`piU d` in place of `subApprox`/`subU`. -/
noncomputable def piUFixIso (d : ApproximableMap U U) :
    {w : U.Element // (piU d).toElementMap w = w} ≃o
      {φ : (funSpace U U).Element // (piD d).toElementMap φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, piD_fix_of_piU_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, piU_fix_of_piD_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap_piU d w.1
    rw [w.2] at hw
    rw [piD_fix_of_piU_fix w.2] at hw
    exact hw.symm
  right_inv φ := by
    apply Subtype.ext
    exact jArrow_comp_iArrow_apply φ.1
  map_rel_iff' := by
    intro w w'
    show jArrow.toElementMap w.1 ≤ jArrow.toElementMap w'.1 ↔ w.1 ≤ w'.1
    constructor
    · intro hle
      have h2 := iArrow.toElementMap_mono hle
      have e1 : iArrow.toElementMap (jArrow.toElementMap w.1) = w.1 := by
        have hw := toElementMap_piU d w.1
        rw [w.2, piD_fix_of_piU_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap_piU d w'.1
        rw [w'.2, piD_fix_of_piU_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle
end

section
/-- `subU`'s defining formula unfolded at the element level. -/
theorem toElementMap_subU (w : U.Element) :
    subU.toElementMap w = iArrow.toElementMap (Sub8_6.subApprox.toElementMap
      (jArrow.toElementMap w)) := by
  unfold subU
  rw [toElementMap_comp, toElementMap_comp]
end

section
/-- Unfolds `subU.toElementMap w = w` (via `jArrow_comp_iArrow`) into the statement that
`j_→(w)` is already a fixed point of `subApprox`. Used for both `subUFixIso.toFun`'s well-typing
and its `left_inv`. -/
theorem subApprox_fix_of_subU_fix {w : U.Element} (hw : subU.toElementMap w = w) :
    Sub8_6.subApprox.toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_subU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep
end

section
theorem subU_fix_of_subApprox_fix {φ : (funSpace U U).Element}
    (hφ : Sub8_6.subApprox.toElementMap φ = φ) :
    subU.toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_subU, jArrow_comp_iArrow_apply, hφ]
end

section
/-- **`Fix(subU) ≃o Fix(subApprox)`.** Forward: `w ↦ j_→(w)`; backward: `φ ↦ i_→(φ)`. Needs only
`j_→∘i_→ = I` (no inequality on `i_→∘j_→`). -/
noncomputable def subUFixIso :
    {w : U.Element // subU.toElementMap w = w} ≃o
      {φ : (funSpace U U).Element // Sub8_6.subApprox.toElementMap φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, subApprox_fix_of_subU_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, subU_fix_of_subApprox_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap_subU w.1
    rw [w.2] at hw
    rw [subApprox_fix_of_subU_fix w.2] at hw
    exact hw.symm
  right_inv φ := by
    apply Subtype.ext
    exact jArrow_comp_iArrow_apply φ.1
  map_rel_iff' := by
    intro w w'
    show jArrow.toElementMap w.1 ≤ jArrow.toElementMap w'.1 ↔ w.1 ≤ w'.1
    constructor
    · intro hle
      have h2 := iArrow.toElementMap_mono hle
      have e1 : iArrow.toElementMap (jArrow.toElementMap w.1) = w.1 := by
        have hw := toElementMap_subU w.1
        rw [w.2, subApprox_fix_of_subU_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap_subU w'.1
        rw [w'.2, subApprox_fix_of_subU_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle
end

section
/-- **`subU`'s fixed points are exactly the finitary projections of `𝒰`** (Exercise 8.27's
opening sentence, precisely): composing `subUFixIso` with Theorem 8.6(b)(ii)'s `subApproxFixIso`
identifies `Fix(subU)` with `{f : 𝒰→𝒰 ∣ sub f = f}`, which by Theorem 8.6(a)'s
`sub_eq_self_iff_isFinitaryProjection` is exactly `{f ∣ FinitaryProjection f}`. -/
noncomputable def subUFixIsoSubFixed :
    {w : U.Element // subU.toElementMap w = w} ≃o
      {f : ApproximableMap U U // sub f = f} :=
  subUFixIso.trans Sub8_6.subApproxFixIso
end

section
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
end

section
/-- **Exercise 8.27(b)(1).** If `piD d` satisfies Scott's step-closure formula (ii), it is a
finitary projection — a direct specialization of `Theorem85.lean`'s general
`isFinitaryProjection_of_formula`, no new proof needed beyond the specialization itself. -/
theorem isFinitaryProjection_piD_of_formula (d : ApproximableMap U U)
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    FinitaryProjection (piD d) :=
  isFinitaryProjection_of_formula (piD d) hii
end

section
/-- **Exercise 8.27(b)(0), corollary: if `piD d` is finitary then so is `piU d`.** Mirrors
`isFinitary_subU`'s use of `subUFixIso`. This is the reduction Exercise 8.27(b)(1)–(b)(4) will
target: it suffices to prove `IsFinitary (piD d)` for `d` polymorphic. -/
theorem isFinitary_piU_of_isFinitary_piD {d : ApproximableMap U U} (h : IsFinitary (piD d)) :
    IsFinitary (piU d) := by
  obtain ⟨β, F, ⟨iso⟩⟩ := h
  exact ⟨β, F, ⟨(piUFixIso d).trans iso⟩⟩
end

section
/-- **Exercise 8.27(b)(1), assembled with (b)(0):** formula (ii) for `piD d` alone gives
`IsFinitary (piU d)`, i.e. (combined with the already-Pass 8.27(a)) the *entire* exercise for `d`
polymorphic. This pins down exactly what Exercise 8.27(b)(2)–(b)(3) need to supply: `hii`. -/
theorem isFinitary_piU_of_formula {d : ApproximableMap U U}
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    IsFinitary (piU d) :=
  isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD_of_formula d hii).out.2
end

section
/-- **`Π(d) ≤ I`, for any `d`.** Chains: `subU(t) ⊑ t` (`subU`'s own projection property) with
`f`'s monotonicity to get `f(subU(t)) ⊑ f(t)`, then the "type at `t`"'s own `≤ I` (from
`isFinitaryProjection_decode_subU`) to get `(type at t)(f(subU(t))) ⊑ f(subU(t))`. -/
theorem le_idMap_piD (d : ApproximableMap U U) : piD d ≤ idMap (funSpace U U) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap, ← (funSpaceEquiv U U).le_iff_le, funSpaceEquiv_apply,
    funSpaceEquiv_apply, toApproxMap_toElementMap_piD, le_iff_toElementMap_le]
  intro t
  rw [toElementMap_piDApply]
  have hP := (isFinitaryProjection_decode_subU (d.toElementMap (subU.toElementMap t))).out.1.2
  calc (toApproxMap (jArrow.toElementMap (subU.toElementMap
        (d.toElementMap (subU.toElementMap t))))).toElementMap
        ((toApproxMap φ).toElementMap (subU.toElementMap t))
      ≤ (toApproxMap φ).toElementMap (subU.toElementMap t) :=
        toElementMap_le_self_of_le_idMap hP _
    _ ≤ (toApproxMap φ).toElementMap t :=
        (toApproxMap φ).toElementMap_mono
          (toElementMap_le_self_of_le_idMap isProjection_subU.2 t)
end

section
/-- Evaluating `piDApply d f` at an already-`subU`-projected point simplifies (via `subU`'s
idempotency) exactly to `toElementMap_piDApply`'s formula with `t` replaced by `subU.toElementMap
t` throughout. The key computational step behind `isRetraction_piD`. -/
theorem piDApply_toElementMap_eq (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap (subU.toElementMap t) =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, toElementMap_idem_of_isRetraction isProjection_subU.1 t]
end

section
/-- **`Π(d)` is a retraction, for any `d`.** -/
theorem isRetraction_piD (d : ApproximableMap U U) : Retraction (piD d) := by
  constructor
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_piD d ((piD d).toElementMap φ),
    toApproxMap_toElementMap_piD d φ]
  apply ApproximableMap.ext_of_toElementMap
  intro t
  rw [toElementMap_piDApply d (piDApply d (toApproxMap φ)) t,
    piDApply_toElementMap_eq d (toApproxMap φ) t,
    toElementMap_piDApply d (toApproxMap φ) t]
  exact toElementMap_idem_of_isRetraction
    (isFinitaryProjection_decode_subU (d.toElementMap (subU.toElementMap t))).out.1.1 _
end

section
/-- **Scott's own hint, in full: `Π(d)` is a projection, for every `d`.** -/
theorem isProjection_piD (d : ApproximableMap U U) : IsProjection (piD d) :=
  ⟨isRetraction_piD d, le_idMap_piD d⟩
end

section
/-- **`Π(d)`, regarded as living in `𝒰` (`piU d`), is a projection, for every `d`.** Half of "for
`d` a polymorphic type, `Π(d)` is a type" (Definition 8.3's `IsProjection` clause) — Scott's own
"it is easy to check" — obtained "for free" from `isProjection_piD` via the same conjugation
gadget (`isProjection_conjArrow`) used for `subU` in Step 1. Note this does not even need `d` to
be a polymorphic type. -/
theorem isProjection_piU (d : ApproximableMap U U) : IsProjection (piU d) :=
  isProjection_conjArrow (isProjection_piD d)
end

section
/-- **`piDType d` is monotone in `s`.** Composite of monotone `toElementMap`s (`d`, `subU`,
`jArrow`) followed by monotone `toApproxMap` (`Sub8_6.toApproxMap_monotone`). -/
theorem piDType_monotone (d : ApproximableMap U U) {s s' : U.Element} (h : s ≤ s') :
    piDType d s ≤ piDType d s' :=
  Sub8_6.toApproxMap_monotone ((piDTypeMap d).toElementMap_mono h)
end

section
/-- **Exercise 8.27(b)(2), specialized to self-relation** (the shape Theorem 8.5's formula (ii)
actually tests, `a.rel X X`): combines (a) and (b) into the single membership-test formula that
Exercise 8.27(b)(3) will chain through `subU`'s and each `D'_s`'s own formula (ii). -/
theorem piD_rel_self_iff (d : ApproximableMap U U) {X : Set (ApproximableMap U U)} :
    (piD d).rel X X ↔ ∃ hX : (funSpace U U).mem X, gSection (piDUncurried d) hX ∈ X := by
  rw [piD_rel_iff]
  exact ⟨fun ⟨hX, _, hmem⟩ => ⟨hX, hmem⟩, fun ⟨hX, hmem⟩ => ⟨hX, hX, hmem⟩⟩
end

section
theorem toElementMap_piDTypeMap (d : ApproximableMap U U) (s : U.Element) :
    (piDTypeMap d).toElementMap s = jArrow.toElementMap (subU.toElementMap (d.toElementMap s)) := by
  unfold piDTypeMap
  rw [toElementMap_comp, toElementMap_comp]
end

section
theorem isFinitaryProjection_piDType (d : ApproximableMap U U) (s : U.Element) :
    FinitaryProjection (piDType d s) := by
  unfold piDType
  rw [toElementMap_piDTypeMap]
  exact isFinitaryProjection_decode_subU (d.toElementMap s)
end

section
/-- `piDApply`'s defining formula, restated via `piDType`/`piDTypeMap`. -/
theorem toElementMap_piDApply' (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (piDType d (subU.toElementMap t)).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, piDType, toElementMap_piDTypeMap]
end

section
/-- **Exercise 8.27(b)(3)(b), single-pair case — the genuine mathematical content.** Given
`f := piDApply d (toApproxMap x)` relates `Y₀` to `Z₀`, produce `X` (a single `step`) with
`x.mem X`, `X ⊆ step Y₀ Z₀`, `(piD d).rel X X`.

The compactness-descent argument, in outline (`t := subU(↑Y₀)`):
1. Formula (ii) for the finitary projection `piDType d t` (at `t`'s own image of `x`) gives `W ⊆ Z₀`
   with `piDType d t` self-relating `W`.
2. Both `(toApproxMap x).rel _ W`'s witness and `(piDType d t).rel W W` are pushed down, via
   `t = ⨆ scPrincipal` and directed-sup compactness, to *some* self-consistent approximants
   `i₀, i₁ ∈ scFamily t`.
3. A common refinement `k` (directedness of `scFamily t`) makes *both* facts hold simultaneously at
   `T := k.1`: `(toApproxMap x).rel T W` (monotonicity) and `(piDType d (scPrincipal k)).rel W W`
   (monotonicity of `piDType d`, since bigger domain element ⟹ bigger map).
4. `scPrincipal k` is *exactly* `subU`-fixed (self-consistency), so `piDType d (scPrincipal k))` is
   *exactly* the type-projection `X`'s own self-test uses at `T` — no mismatch. -/
theorem exists_X_of_mem_step (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y₀ Z₀ : Set ℚ} (hmem : piDApply d (toApproxMap x) ∈ step Y₀ Z₀) :
    ∃ X, x.mem X ∧ X ⊆ (step Y₀ Z₀ : Set (ApproximableMap U U)) ∧ (piD d).rel X X := by
  have hrelY0Z0 : (piDApply d (toApproxMap x)).rel Y₀ Z₀ := hmem
  have hY₀ : U.mem Y₀ := (piDApply d (toApproxMap x)).rel_dom hrelY0Z0
  have hZ₀ : U.mem Z₀ := (piDApply d (toApproxMap x)).rel_cod hrelY0Z0
  set t : U.Element := subU.toElementMap (U.principal hY₀) with ht_def
  have ht : subU.toElementMap t = t := toElementMap_idem_of_isRetraction isProjection_subU.1 _
  have hmem' : ((piDType d t).toElementMap ((toApproxMap x).toElementMap t)).mem Z₀ := by
    have h := ((piDApply d (toApproxMap x)).rel_iff_mem_principal hY₀).mp hrelY0Z0
    rwa [toElementMap_piDApply'] at h
  obtain ⟨_, W, hW_mem, hWZ₀, hWW⟩ :=
    (formula_of_isFinitaryProjection (isFinitaryProjection_piDType d t)
      ((toApproxMap x).toElementMap t)).mp hmem'
  have hw_sup := eq_iSupDirected_scPrincipal ht
  -- Push the continuity witness `W` for `x` down to a single self-consistent approximant `i₀`.
  rw [hw_sup, toElementMap_iSupDirected, mem_iSupDirected] at hW_mem
  obtain ⟨i₀, hi₀⟩ := hW_mem
  have hrelT0 : (toApproxMap x).rel i₀.1 W :=
    (rel_iff_mem_principal (toApproxMap x) (t.sub i₀.2.2)).mpr hi₀
  -- Push the self-relation witness `W` for `piDType d t` down to a single self-consistent `i₁`.
  have hWW2 : ∃ i : scFamily t, (piDType d (scPrincipal i)).rel W W := by
    have h2 : (piDType d t).rel W W := hWW
    unfold piDType at h2
    rw [hw_sup, toElementMap_iSupDirected, Sub8_6.toApproxMap_rel_iSupDirected] at h2
    exact h2
  obtain ⟨i₁, hi₁⟩ := hWW2
  -- Common refinement `k` of `i₀, i₁` makes both facts hold simultaneously.
  obtain ⟨k, hik0, hik1⟩ := scFamily_directed ht i₀ i₁
  have hksub0 : k.1 ⊆ i₀.1 := (U.principal_le_iff (t.sub i₀.2.2) (t.sub k.2.2)).mp hik0
  have hTfinal : U.mem k.1 := subU.rel_dom k.2.1
  have hWmem : U.mem W := (piDType d t).rel_dom hWW
  have hrelTfinal : (toApproxMap x).rel k.1 W :=
    (toApproxMap x).mono hrelT0 hksub0 subset_rfl hTfinal hWmem
  have hPfinal : (piDType d (scPrincipal k)).rel W W := piDType_monotone d hik1 W W hi₁
  -- `k.1` is `subU`-self-consistent, so `scPrincipal k = subU(↑k.1)` exactly.
  have hTfinal_fix : subU.toElementMap (U.principal hTfinal) = U.principal hTfinal :=
    subU_principal_eq_of_rel_self hTfinal k.2.1
  set X : Set (ApproximableMap U U) := step k.1 W with hX_def
  have hXvalid : (funSpace U U).mem X := step_mem hTfinal hWmem
  refine ⟨X, ?_, ?_, ?_⟩
  · -- `x.mem X`
    exact toApproxMap_rel.mp hrelTfinal
  · -- `X ⊆ step Y₀ Z₀`
    have hle : t ≤ U.principal hY₀ := toElementMap_le_self_of_le_idMap isProjection_subU.2 _
    have hY0sub : Y₀ ⊆ k.1 := ((U.mem_principal hY₀).mp (hle k.1 k.2.2)).2
    exact step_subset hY₀ hZ₀ hY0sub hWZ₀
  · -- `(piD d).rel X X`
    rw [piD_rel_self_iff]
    refine ⟨hXvalid, ?_⟩
    show (gSection (piDUncurried d) hXvalid).rel k.1 W
    rw [gSection_piDUncurried_rel_iff d hXvalid hTfinal]
    set g : ApproximableMap U U := toApproxMap ((funSpace U U).principal hXvalid) with hg_def
    show ((piDApply d g).toElementMap (U.principal hTfinal)).mem W
    rw [toElementMap_piDApply', hTfinal_fix]
    have hg : g.rel k.1 W := by
      rw [hg_def, toApproxMap_rel]
      exact ((funSpace U U).mem_principal hXvalid).mpr ⟨hXvalid, subset_rfl⟩
    have hgmem : (g.toElementMap (U.principal hTfinal)).mem W :=
      (rel_iff_mem_principal g hTfinal).mp hg
    exact mem_of_exists_rel_self (g.toElementMap (U.principal hTfinal))
      ((piDType d (U.principal hTfinal)).rel_dom hPfinal) hgmem subset_rfl hPfinal
end

section
/-- **Exercise 8.27(b)(3)(b), assembled over a whole `stepFun` list.** Induction on the list `L`
using `exists_X_of_mem_step` for the head pair and the inductive hypothesis for the tail, combined
via `x.inter_mem` (giving the ambient validity of the intersection "for free", `x.sub`) and
`(piD d).mono`/`.inter_right` (self-relation of an intersection of two self-related nbhds). -/
theorem exists_X_of_mem_stepFun (d : ApproximableMap U U) (x : (funSpace U U).Element)
    (L : List (Set ℚ × Set ℚ)) (hmem : piDApply d (toApproxMap x) ∈ stepFun L) :
    ∃ X, x.mem X ∧ X ⊆ (stepFun L : Set (ApproximableMap U U)) ∧ (piD d).rel X X := by
  induction L with
  | nil =>
    refine ⟨(funSpace U U).master, x.master_mem, ?_, (piD d).master_rel⟩
    simp
  | cons p L ih =>
    rw [stepFun_cons] at hmem
    obtain ⟨hmemP, hmemL⟩ := hmem
    obtain ⟨Xp, hXpx, hXpsub, hXpXp⟩ := exists_X_of_mem_step d x hmemP
    obtain ⟨XL, hXLx, hXLsub, hXLXL⟩ := ih hmemL
    refine ⟨Xp ∩ XL, x.inter_mem hXpx hXLx, ?_, ?_⟩
    · rw [stepFun_cons]
      exact Set.inter_subset_inter hXpsub hXLsub
    · have hvalidP : (funSpace U U).mem Xp := x.sub hXpx
      have hvalidL : (funSpace U U).mem XL := x.sub hXLx
      have hvalidInter : (funSpace U U).mem (Xp ∩ XL) := x.sub (x.inter_mem hXpx hXLx)
      have h1 : (piD d).rel (Xp ∩ XL) Xp :=
        (piD d).mono hXpXp Set.inter_subset_left subset_rfl hvalidInter hvalidP
      have h2 : (piD d).rel (Xp ∩ XL) XL :=
        (piD d).mono hXLXL Set.inter_subset_right subset_rfl hvalidInter hvalidL
      exact (piD d).inter_right h1 h2
end

section
/-- **Exercise 8.27(b)(3), the `⟹` half, closed for any `d` at all.** Destructure the general
`Y : Set (ApproximableMap U U)` via `funSpace_mem_iff` into `Y = stepFun L`, then apply
`exists_X_of_mem_stepFun`. -/
theorem hii_hard_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    (hmem : piDApply d (toApproxMap x) ∈ Y) :
    ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hYE
  exact exists_X_of_mem_stepFun d x L hmem
end

section
/-- **Exercise 8.27(b)(3), in full: `piD d` satisfies Scott's step-closure formula (ii), for *any*
`d` at all** (`d`'s polymorphism is not needed). Combines the reduction (b)(3)(a) with the easy
(`hii_easy_direction`) and now-closed hard (`hii_hard_direction`) halves. -/
theorem hii_piD (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  rw [piD_toElementMap_mem_iff]
  constructor
  · rintro ⟨hYE, hmem⟩
    exact ⟨hYE, hii_hard_direction d x hYE hmem⟩
  · rintro ⟨hYE, X, hXx, hXY, hXX⟩
    have := hii_easy_direction d x hYE hXx hXY hXX
    rwa [piD_toElementMap_mem_iff] at this
end

section
/-- **Exercise 8.27(b)(4): `piD d` is a finitary projection, for every `d`** (Exercise 8.27(b)(1)
specialized to `hii_piD`). Combined with Exercise 8.27(b)(0) (`isFinitary_piU_of_isFinitary_piD`),
this closes "`Π(d)` is a type" — Scott's own hint, in full, and *without even needing `d` to be a
polymorphic type* (a strictly stronger statement than the exercise asks for). -/
theorem isFinitaryProjection_piD (d : ApproximableMap U U) : FinitaryProjection (piD d) :=
  isFinitaryProjection_piD_of_formula d (fun x => hii_piD d x)
end

section
/-- **Exercise 8.27, in full: for `d` a polymorphic type, `Π(d)` is a type.** (In fact for *any*
`d` at all — see `isFinitaryProjection_piD`.) This is the exercise's own statement, the last exercise
in the book, closed. -/
theorem isFinitaryProjection_piU (d : ApproximableMap U U) : FinitaryProjection (piU d) :=
  ⟨⟨isProjection_piU d, isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD d).out.2⟩⟩
end

section
set_option linter.unusedVariables false

theorem example_827 : And
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
    (∀
      {d :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsFinitary
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (DomainTheory.NeighbourhoodSystems.piD d) →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.piU d)))
  (∀
    (d :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
    {X :
      Set
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (DomainTheory.NeighbourhoodSystems.piD d) X X)
      (∃ (hX :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          X),
        @Membership.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          (@Set.instMembership
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          X
          (@DomainTheory.NeighbourhoodSystems.gSection
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            Rat Rat
            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX))) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
    (∀
      {d :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsFinitary
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (DomainTheory.NeighbourhoodSystems.piD d) →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.piU d)))
  (∀
    (d :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
    {X :
      Set
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (DomainTheory.NeighbourhoodSystems.piD d) X X)
      (∃ (hX :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          X),
        @Membership.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          (@Set.instMembership
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          X
          (@DomainTheory.NeighbourhoodSystems.gSection
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            Rat Rat
            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
    (∀
      {d :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsFinitary
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (DomainTheory.NeighbourhoodSystems.piD d) →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.piU d))
    (@And.intro
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d))
      (@And.intro
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d))
        (@And.intro
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d))
          (@And.intro
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d))
            (@And.intro
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X)))))
              (@And.intro
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                (@And.intro
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                  (@And.intro
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y)
                    (@And.intro
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)))))
                      (@And.intro
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z))
                        (@And.intro
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX))))
                          DomainTheory.NeighbourhoodSystems.exists_X_of_mem_step
                          DomainTheory.NeighbourhoodSystems.piD_rel_iff)
                        DomainTheory.NeighbourhoodSystems.gSection_piDUncurried_rel_iff)
                      DomainTheory.NeighbourhoodSystems.piD_toElementMap_mem_iff)
                    DomainTheory.NeighbourhoodSystems.hii_easy_direction)
                  DomainTheory.NeighbourhoodSystems.exists_X_of_mem_stepFun)
                DomainTheory.NeighbourhoodSystems.hii_hard_direction)
              DomainTheory.NeighbourhoodSystems.hii_piD)
            DomainTheory.NeighbourhoodSystems.isFinitaryProjection_piD)
          DomainTheory.NeighbourhoodSystems.isFinitaryProjection_piD_of_formula)
        DomainTheory.NeighbourhoodSystems.isFinitaryProjection_piU)
      @DomainTheory.NeighbourhoodSystems.isFinitary_piU_of_formula)
    @DomainTheory.NeighbourhoodSystems.isFinitary_piU_of_isFinitary_piD)
  DomainTheory.NeighbourhoodSystems.piD_rel_self_iff
end

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

section
theorem foldl_ratMax (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMaxCode (Nat.pair acc x.unpair.2)) z)
      = (l.map decodeRatPair).foldl (fun acc p => max acc p.2) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMaxCode]
    rfl
end

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

section
theorem maxSnd_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => max acc p.2) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => max acc q.2) seed = p.2 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total a.2 seed with hle | hle
    · rw [max_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [max_eq_right hle]
      rcases ih a.2 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
end

end foldl
open Domain.Recursive NeighborhoodSystem

section
/-- **Every pair of `decodeQPairList (canonCode c)` has both endpoints in `[0, 1]`** — mirrors
`forall_lt_decodeQPairList_canonCode` (nondegeneracy), giving the companion boundedness fact. -/
theorem forall_bounds_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), 0 ≤ p.1 ∧ p.2 ≤ 1 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro p hp
    obtain ⟨p0, -, -, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact ⟨le_sup_right, inf_le_right⟩
end

section
/-- `max_i pᵢ.2` over a presenting list, folded with seed `0`. -/
def listMaxSnd (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => max acc p.2) 0
end

section
/-- `min_i pᵢ.1` over a presenting list, folded with seed `1` (safe: every genuine pair has
`p.1 < 1` once bounded, `forall_bounds_decodeQPairList_canonCode`). -/
def listMinFst (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => min acc p.1) 1
end

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

section
/-- Bridging `List.foldl` over raw pair-codes (via `ratMinCode`) to `List.foldl` over decoded
pairs (via `min ·.1`), one step at a time. -/
theorem foldl_ratMin (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMinCode (Nat.pair acc x.unpair.1)) z)
      = (l.map decodeRatPair).foldl (fun acc p => min acc p.1) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMinCode]
    rfl
end

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

section
theorem maxSnd_seed_le (L : List (ℚ × ℚ)) (seed : ℚ) :
    seed ≤ L.foldl (fun acc p => max acc p.2) seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (le_max_left seed a.2).trans (ih (max seed a.2))
end

end foldl
open Domain.Recursive NeighborhoodSystem

section
/-- The code-level `listMaxSnd`: fold `ratMaxCode` over `c`'s pair-codes, seeded at `zeroCode`. -/
def listMaxSndCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) 0 zeroCode c
end

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

section
theorem listMaxSndCode (c : ℕ) :
    decodeRat (_root_.DomainTheory.NeighbourhoodSystems.listMaxSndCode c) = listMaxSnd (decodeQPairList c) := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.listMaxSndCode listMaxSnd decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMaxCode (Nat.pair acc x.unpair.2)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat.foldl_ratMax, decodeRat_zeroCode]
end

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

section
theorem maxSnd_ge (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    p.2 ≤ L.foldl (fun acc q => max acc q.2) seed := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (le_max_right seed p.2).trans (foldl.maxSnd_seed_le l (max seed p.2))
    · exact ih (max seed a.2) hp'
end

end foldl
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

section
theorem ge {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : p.2 ≤ listMaxSnd L :=
  foldl.maxSnd_ge L 0 p hp
end

section
theorem attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hlb : ∀ p ∈ L, 0 < p.2) :
    ∃ p ∈ L, p.2 = listMaxSnd L := by
  rcases foldl.maxSnd_mem_or_eq_seed L 0 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMaxSnd.ge hp0) (not_le.mpr (hlb p0 hp0))
  · exact ⟨p, hp, h1.symm⟩
end

end listMaxSnd
open Domain.Recursive NeighborhoodSystem

section
/-- The code-level `listMinFst`: fold `ratMinCode` over `c`'s pair-codes, seeded at `oneCode`. -/
def listMinFstCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) 0 oneCode c
end

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

section
theorem listMinFstCode (c : ℕ) :
    decodeRat (_root_.DomainTheory.NeighbourhoodSystems.listMinFstCode c) = listMinFst (decodeQPairList c) := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.listMinFstCode listMinFst decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMinCode (Nat.pair acc x.unpair.1)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat.foldl_ratMin, decodeRat_oneCode]
end

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

section
theorem minFst_le_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed ≤ seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (ih (min seed a.1)).trans (min_le_left seed a.1)
end

end foldl
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

section
/-- **`listMaxSnd L` is arbitrarily approached from below by `presentedIntervals L`.** -/
theorem tight {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) {y : ℚ}
    (hy : y < listMaxSnd L) : ∃ x ∈ presentedIntervals L, y < x := by
  have hlb : ∀ p ∈ L, 0 < p.2 := fun p hp => lt_of_le_of_lt (hb p hp).1 (hpos p hp)
  obtain ⟨p, hp, hpeq⟩ := listMaxSnd.attained hne hlb
  rw [← hpeq] at hy
  rcases lt_or_ge y p.1 with hlt | hge
  · exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hpos p hp⟩, hlt⟩
  · exact ⟨(y + p.2) / 2, mem_presentedIntervals.mpr ⟨p, hp, hge.trans (left_lt_add_div_two.mpr hy).le,
      add_div_two_lt_right.mpr hy⟩, left_lt_add_div_two.mpr hy⟩
end

end listMaxSnd
open Domain.Recursive NeighborhoodSystem

section
/-- The midpoint code of `canonCode n`'s intrinsic `(min, max)` pair. -/
def splitU2MidCode (n : ℕ) : ℕ :=
  ratMidCode (Nat.pair (listMinFstCode (canonCode n)) (listMaxSndCode (canonCode n)))
end

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

section
theorem splitU2MidCode (n : ℕ) :
    decodeRat (_root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode n) =
      (listMinFst (decodeQPairList (canonCode n)) + listMaxSnd (decodeQPairList (canonCode n)))
        / 2 := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode
  rw [decodeRat_ratMidCode', unpair_pair_fst, unpair_pair_snd, decodeRat.listMinFstCode,
    decodeRat.listMaxSndCode]
end

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

section
theorem minFst_le (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    L.foldl (fun acc q => min acc q.1) seed ≤ p.1 := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (foldl.minFst_le_seed l (min seed p.1)).trans (min_le_right seed p.1)
    · exact ih (min seed a.1) hp'
end

end foldl
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

section
theorem le {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : listMinFst L ≤ p.1 :=
  foldl.minFst_le L 1 p hp
end

end listMinFst
namespace splitU2
open Domain.Recursive NeighborhoodSystem

section
/-- **`Xₙ`'s intrinsic minimum is strictly below its intrinsic maximum**, via any single
witnessing pair of `canonCode n`'s presenting list (nonempty, `forall_lt_...`). -/
theorem min_lt_max (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < listMaxSnd (decodeQPairList (canonCode n)) := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (decodeQPairList_canonCode_ne_nil n)
  exact lt_of_le_of_lt (listMinFst.le hp)
    (lt_of_lt_of_le (forall_lt_decodeQPairList_canonCode n p hp) (listMaxSnd.ge hp))
end

section
theorem mid_lt_max (n : ℕ) :
    decodeRat (splitU2MidCode n) < listMaxSnd (decodeQPairList (canonCode n)) := by
  rw [decodeRat.splitU2MidCode]; exact add_div_two_lt_right.mpr (splitU2.min_lt_max n)
end

section
theorem min_lt_mid (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < decodeRat (splitU2MidCode n) := by
  rw [decodeRat.splitU2MidCode]; exact left_lt_add_div_two.mpr (splitU2.min_lt_max n)
end

end splitU2
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

section
/-- **`listMaxSnd L` strictly upper-bounds `presentedIntervals L`.** -/
theorem upper_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    x < listMaxSnd L := by
  obtain ⟨p, hp, -, hx2⟩ := mem_presentedIntervals.mp hx
  exact hx2.trans_le (listMaxSnd.ge hp)
end

end listMaxSnd
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

section
/-- **`listMinFst L` lower-bounds `presentedIntervals L`.** -/
theorem lower_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    listMinFst L ≤ x := by
  obtain ⟨p, hp, hx1, -⟩ := _root_.DomainTheory.NeighbourhoodSystems.mem_presentedIntervals.mp hx
  exact (listMinFst.le hp).trans hx1
end

end listMinFst
open Domain.Recursive NeighborhoodSystem

section
/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
intrinsic `(min, max)`. -/
def splitU2Left (n : ℕ) : ℕ := clipLtListCode (splitU2MidCode n) (canonCode n)
end

namespace foldl
open Domain.Recursive NeighborhoodSystem

section
theorem minFst_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => min acc q.1) seed = p.1 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total seed a.1 with hle | hle
    · rw [min_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [min_eq_right hle]
      rcases ih a.1 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
end

end foldl
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

section
theorem attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hub : ∀ p ∈ L, p.1 < 1) :
    ∃ p ∈ L, p.1 = listMinFst L := by
  rcases foldl.minFst_mem_or_eq_seed L 1 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMinFst.le hp0) (not_le.mpr (hub p0 hp0))
  · exact ⟨p, hp, h1.symm⟩
end

end listMinFst
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

section
/-- **`listMaxSnd` is a well-defined function of the presented set alone.** -/
theorem congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMaxSnd L1 = listMaxSnd L2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨x, hx, hyx⟩ := listMaxSnd.tight hne2 hpos2 hb2 hlt
    have hx1 : x ∈ presentedIntervals L1 := heq.symm ▸ hx
    exact absurd (listMaxSnd.upper_bound hx1) (not_lt.mpr hyx.le)
  · obtain ⟨x, hx, hyx⟩ := listMaxSnd.tight hne1 hpos1 hb1 hlt
    have hx2 : x ∈ presentedIntervals L2 := heq ▸ hx
    exact absurd (listMaxSnd.upper_bound hx2) (not_lt.mpr hyx.le)
end

end listMaxSnd
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

section
/-- **`listMinFst L` is the genuine minimum of `presentedIntervals L`** (membership half). -/
theorem mem_presentedIntervals {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) :
    listMinFst L ∈ presentedIntervals L := by
  have hub : ∀ p ∈ L, p.1 < 1 := fun p hp => (hpos p hp).trans_le (hb p hp).2
  obtain ⟨p, hp, hpeq⟩ := listMinFst.attained hne hub
  exact _root_.DomainTheory.NeighbourhoodSystems.mem_presentedIntervals.mpr ⟨p, hp, hpeq.le, hpeq ▸ hpos p hp⟩
end

section
/-- **`listMinFst` is a well-defined function of the presented set alone**, mirroring
`MinLevel.lean`'s `minLevel_unique` for `V`: two (nonempty, nondegenerate, `[0,1]`-bounded)
presenting lists of the *same* set have the same `listMinFst`. -/
theorem congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMinFst L1 = listMinFst L2 := by
  have hm1 : listMinFst L1 ∈ presentedIntervals L2 :=
    heq ▸ listMinFst.mem_presentedIntervals hne1 hpos1 hb1
  have hm2 : listMinFst L2 ∈ presentedIntervals L1 :=
    heq ▸ listMinFst.mem_presentedIntervals hne2 hpos2 hb2
  exact le_antisymm (listMinFst.lower_bound hm2) (listMinFst.lower_bound hm1)
end

end listMinFst
open Domain.Recursive NeighborhoodSystem

section
/-- **`splitU2Left`/`splitU2Right`'s midpoint depends only on `UX n` as a set** — the key lemma
that `SplitU.lean`'s `splitULeft`/`splitURight` lack, via `listMinFst.congr`/`listMaxSnd.congr`. -/
theorem splitU2MidCode_congr {n n' : ℕ} (h : UX n = UX n') :
    decodeRat (splitU2MidCode n) = decodeRat (splitU2MidCode n') := by
  have heqP : presentedIntervals (decodeQPairList (canonCode n))
      = presentedIntervals (decodeQPairList (canonCode n')) := h
  have hminEq := listMinFst.congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  have hmaxEq := listMaxSnd.congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  rw [decodeRat.splitU2MidCode, decodeRat.splitU2MidCode, hminEq, hmaxEq]
end

section
/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitU2Right (n : ℕ) : ℕ := clipGeListCode (splitU2MidCode n) (canonCode n)
end

section
theorem UX_splitU2Right (n : ℕ) :
    UX (splitU2Right n) = UX n ∩ Set.Ici (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Right n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxgt⟩ := listMaxSnd.tight (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
        (splitU2.mid_lt_max n)
      exact ⟨x, hx, hxgt.le⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Right n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl
end

section
/-- **`splitU2Right`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Right_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Right n) = UX (splitU2Right n') := by
  rw [UX_splitU2Right, UX_splitU2Right, h, splitU2MidCode_congr h]
end

section
theorem UX_splitU2Left (n : ℕ) :
    UX (splitU2Left n) = UX n ∩ Set.Iio (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Left n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨listMinFst (decodeQPairList (canonCode n)), ?_, splitU2.min_lt_mid n⟩
      exact listMinFst.mem_presentedIntervals (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Left n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl
end

namespace splitU2
open Domain.Recursive NeighborhoodSystem

section
/-- **Disjointness**: `splitU2Left`/`splitU2Right` cover disjoint pieces. -/
theorem disjoint (n : ℕ) : UX (splitU2Left n) ∩ UX (splitU2Right n) = ∅ := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)
end

section
/-- **Covering**: `splitU2Left`/`splitU2Right` reunite to `Xₙ`. -/
theorem union (n : ℕ) : UX (splitU2Left n) ∪ UX (splitU2Right n) = UX n := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitU2MidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩
end

end splitU2
open Domain.Recursive NeighborhoodSystem

section
/-- **`splitU2Left`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Left_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Left n) = UX (splitU2Left n') := by
  rw [UX_splitU2Left, UX_splitU2Left, h, splitU2MidCode_congr h]
end

section
theorem zero_le_listMaxSnd (L : List (ℚ × ℚ)) : 0 ≤ listMaxSnd L := foldl.maxSnd_seed_le L 0
end

namespace primrec
open Domain.Recursive NeighborhoodSystem

section
theorem listMaxSndCode : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.listMaxSndCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) :=
    (primrec_ratMaxCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const zeroCode) primrec_id).of_eq
    fun _ => rfl
end

section
theorem listMinFstCode : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.listMinFstCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) :=
    (primrec_ratMinCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const oneCode) primrec_id).of_eq
    fun _ => rfl
end

section
theorem splitU2MidCode : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode :=
  (primrec_ratMidCode.comp
    ((primrec.listMinFstCode.comp primrec_canonCode).pair
      (primrec.listMaxSndCode.comp primrec_canonCode))).of_eq fun n => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode]
end

section
theorem splitU2Left : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.splitU2Left :=
  (primrec_clipLtListCode.comp (primrec.splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [_root_.DomainTheory.NeighbourhoodSystems.splitU2Left, unpair_pair_fst, unpair_pair_snd]
end

section
theorem splitU2Right : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.splitU2Right :=
  (primrec_clipGeListCode.comp (primrec.splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [_root_.DomainTheory.NeighbourhoodSystems.splitU2Right, unpair_pair_fst, unpair_pair_snd]
end

end primrec
open Domain.Recursive NeighborhoodSystem

section
/-- **`U`'s computable canonical bisection, packaged as a `ComputableBisection`** — the missing
`(f)`-side prerequisite, fixing `SplitU.lean`'s `left_congr`/`right_congr` gap (see the module
docstring). -/
def UBisection2 : ComputableBisection UComputablePresentation where
  left := splitU2Left
  right := splitU2Right
  left_primrec := primrec.splitU2Left
  right_primrec := primrec.splitU2Right
  disjoint := splitU2.disjoint
  union := splitU2.union
  left_congr := fun _ _ h => splitU2Left_congr h
  right_congr := fun _ _ h => splitU2Right_congr h
end

namespace listMinFst
open Domain.Recursive NeighborhoodSystem

section
theorem le_one (L : List (ℚ × ℚ)) : listMinFst L ≤ 1 := foldl.minFst_le_seed L 1
end

end listMinFst
open Domain.Recursive NeighborhoodSystem

section
/-- The difference index: `canonIdx` of the raw difference code `VdiffRaw`. -/
def Vdiff (n m : ℕ) : ℕ := canonIdx (VdiffRaw n m)
end

namespace levelSet
open Domain.Recursive NeighborhoodSystem

section
/-- **The "same level" set-difference formula**, mirroring `Exercise812.lean`'s
`levelSet.inter_same_level` exactly (`&&&` becomes the "and-not" combinator `a ^^^ (a &&& b)`,
via `testBit.xor_and_self`). -/
theorem diff_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ \ levelSet k m₂ = levelSet k (m₁ ^^^ (m₁ &&& m₂)) := by
  ext n; simp [levelSet]
end

section
/-- **Computable version of `levelSet.diff_same_level`, upsampled to a common level** — mirrors
`levelSet.myInter` exactly, substituting `myAndNot` for `myLand`. -/
theorem myDiff (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 \ levelSet k2 m2
      = levelSet (max k1 k2) (myAndNot (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) (m := m1),
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) (m := m2)]
  rw [levelSet.diff_same_level, myAndNot_eq]
end

section
/-- **`VdiffRaw` realizes `VX n \ VX m`** at the `levelSet` level (unconditionally). -/
theorem VdiffRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VdiffRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VdiffRaw n m).unpair.2 = VX n \ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VdiffRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myDiff (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm
end

end levelSet
namespace Vdiff
open Domain.Recursive NeighborhoodSystem

section
/-- **Scott's consistency condition for `\` reduces to non-emptiness**, mirroring
`Vcons_iff_nonempty_inter`. -/
theorem iff_nonempty (n m : ℕ) :
    (∃ k, VX k = VX n \ VX m) ↔ (VX n \ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact VX_nonempty k
  · intro hne
    rw [← levelSet.VdiffRaw] at hne
    have hVmem : V.mem (VX n \ VX m) := by
      rw [← levelSet.VdiffRaw]
      exact ⟨(VdiffRaw n m).unpair.1, (VdiffRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, hk⟩
end

section
theorem spec {n m : ℕ} (h : ∃ k, VX k = VX n \ VX m) : VX (Vdiff n m) = VX n \ VX m := by
  have hne : (levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VdiffRaw]; obtain ⟨k, hk⟩ := h; rw [← hk]; exact VX_nonempty k
  unfold Vdiff
  rw [VX_canonIdx]
  show levelSet (canonIdx (VdiffRaw n m)).unpair.1 (canonIdx (VdiffRaw n m)).unpair.2 = VX n \ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VdiffRaw]
end

end Vdiff
namespace primrec
open Domain.Recursive NeighborhoodSystem

section
theorem lowXor : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.lowXor t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp
    (primrec_add₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right))).of_eq
    fun _ => rfl
end

section
theorem xorStep : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => _root_.DomainTheory.NeighbourhoodSystems.lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec.lowXor.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl
end

section
theorem myXor : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myXor t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.xorStep w.unpair.2.unpair.2) :=
    primrec.xorStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl
end

section
theorem myAndNot : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myAndNot t.unpair.1 t.unpair.2) := by
  have hland : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myLand t.unpair.1 t.unpair.2) := primrec.myLand
  exact (primrec.myXor.comp (Nat.Primrec.left.pair hland)).of_eq fun t => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.myAndNot, unpair_pair_fst, unpair_pair_snd]
end

section
theorem VdiffRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VdiffRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1) := primrec.canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2) := primrec.canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) :=
    (primrec.myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) :=
    (primrec.myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have handnot : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myAndNot
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec.myAndNot.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair handnot).of_eq fun _ => rfl
end

end primrec
open Domain.Recursive NeighborhoodSystem

section
/-- **7.1(i)-for-`\`, for `V`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable. -/
theorem V_diff_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n \ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VdiffRaw t.unpair.1 t.unpair.2) := primrec.VdiffRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec.myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    have := myLevelSetNonempty.le_one (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    rw [unpair_pair_fst, unpair_pair_snd, Vdiff.iff_nonempty, ← levelSet.VdiffRaw,
      myLevelSetNonempty.eq_one_iff]
end

namespace primrec
open Domain.Recursive NeighborhoodSystem

section
theorem Vdiff : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vdiff t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VdiffRaw).of_eq fun _ => rfl
end

end primrec
open Domain.Recursive NeighborhoodSystem

section
/-- **`V` has a computable `\`**, the missing prerequisite for Exercise 8.12(f). -/
def V_isComputableDiff : IsComputableDiff VComputablePresentation where
  diffIdx := Vdiff
  diffIdx_primrec := primrec.Vdiff
  diffIdx_spec := Vdiff.spec
  diff_computable := V_diff_computable
end

section
/-- **`splitX812f`: the exercise's literal target split**, `V` as prober against `U`'s canonical
bisection (`UBisection2`). -/
noncomputable def splitX812f : Set ℕ → Set ℚ → Set ℕ → Set ℚ × Set ℚ :=
  ComputableBisection.splitFromBisection VComputablePresentation V_isComputableDiff UBisection2
    U_noMinimal
end

namespace isComputableSplit
open Domain.Recursive NeighborhoodSystem

section
/-- **Exercise 8.12(f), completed in full**: `splitX812f` satisfies `IsComputableSplit`, the
mirror image of `Exercise812eD.lean`'s `isComputableSplit.812e`. `noncomputable def`, not
`theorem` — `IsComputableSplit` is a data-carrying structure (its `posIdx`/`negIdx` fields are
`ℕ`-valued functions), exactly as `isComputableSplit.812e` itself. -/
noncomputable def «812f» :
    IsComputableSplit VComputablePresentation UComputablePresentation splitX812f :=
  ComputableBisection.isComputableSplit.ofBisection VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed
end

end isComputableSplit
open Domain.Recursive NeighborhoodSystem

section
/-- The union index: list-concatenate the two canonicalized presenting lists. `UX` re-canonicalizes
on lookup, so no further canonicalization of the inputs is needed here (mirrors `Udiff`). -/
def Uunion (n m : ℕ) : ℕ := appendListCode (canonCode n) (canonCode m)
end

section
/-- The union index: `canonIdx` of the raw union code `VunionRaw`. -/
def Vunion (n m : ℕ) : ℕ := canonIdx (VunionRaw n m)
end

section
/-- `hX0`: index `0` presents `U`'s master neighbourhood. `decodeQPairList 0 = []`
(`decodeList_zero`), so `canonList` falls back to its `[(0,1)]` branch, which presents
`U.master` exactly as in `U_mem_presentedIntervals_canonList`. -/
theorem UX_zero : UX 0 = U.master := by
  rw [UX_eq]
  have hL : decodeQPairList 0 = [] := by
    unfold decodeQPairList; rw [decodeList_zero]; rfl
  rw [hL, canonList_eq_of_filter_eq_nil (by simp), presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]
  rfl
end

namespace Uunion
open Domain.Recursive NeighborhoodSystem

section
theorem primrec : Nat.Primrec (fun t : ℕ => Uunion t.unpair.1 t.unpair.2) := by
  unfold Uunion
  exact (primrec_appendListCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
end

end Uunion
open Domain.Recursive NeighborhoodSystem

section
/-- `hD₁mne` for `V`: the master neighbourhood `V.master = Set.univ` is non-empty. -/
theorem V_master_nonempty : V.master.Nonempty := Set.univ_nonempty
end

section
/-- `hD₀mne` for `U`: the master neighbourhood `U.master = Set.Ico 0 1` is non-empty. -/
theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩
end

namespace Uunion
open Domain.Recursive NeighborhoodSystem

section
/-- **`Uunion` realizes set union at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — concatenating presenting lists always presents the union, no consistency case
split needed (the one respect in which `∪` is even simpler than `\`'s `Udiff.eq_diff`). -/
theorem eq_union (n m : ℕ) :
    presentedIntervals (decodeQPairList (Uunion n m)) = UX n ∪ UX m := by
  unfold Uunion
  rw [decodeQPairList_appendListCode, presentedIntervals_append]
  rfl
end

end Uunion
section
open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)


namespace splitFromBisection
/-- **`splitFromBisection` satisfies `SplitSpec'`**, completing the concrete-construction half of
`8.12(g)(3)`. Needs one extra hypothesis beyond `isComputableSplit.ofBisection`'s own,
`hQne : ∀ j, Q.X j ≠ ∅` — true for both `U`/`V` (every `ComputablePresentation` index is `mem`-
genuine, and both systems' `mem` structurally excludes `∅`; see `Exercise812.lean` line 199/
`Definition87.lean` line 96) but not derivable from `ComputableBisection`'s abstract fields alone
(nothing there stops `Q.X (B.left m)`, say, from being `∅` in general — only used in the "neither
decider fires" branch, to show the bisection's two halves are each individually `≠ ∅`, matching that
branch's `A ∩ Xn ≠ ∅ ↔ .1 ≠ ∅`/`A \ Xn ≠ ∅ ↔ .2 ≠ ∅` obligations). The two decider-fires branches
need no such hypothesis at all — `.1`/`.2` there are literally `∅`/`B'`, and the requisite `↔`s
reduce to `hAB` via the algebraic facts `A ∩ Xn = ∅ → A \ Xn = A` (resp. `A \ Xn = ∅ → A ∩ Xn = A`).
The "not presented" branch reduces to exactly `splitChoice'_isSplitSpec` (`Exercise812c.lean`),
verbatim. -/
theorem isSplitSpec' (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hQne : ∀ j, Q.X j ≠ ∅) :
    SplitSpec' W (splitFromBisection P hDiff B hWnomin) := by
  intro A B' hAB hBW Xn
  by_cases h : ∃ n m k, A = P.X n ∧ B' = Q.X m ∧ Xn = P.X k
  · obtain ⟨n, m, k, rfl, rfl, rfl⟩ := h
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k]
    by_cases h1 : emptyInterDec P (Nat.pair n k) = 1
    · have hInterEmpty : P.X n ∩ P.X k = ∅ := (emptyInterDec.eq_one_iff P hpos hnomin n k).mp h1
      have hdiffEq : P.X n \ P.X k = P.X n := by
        ext x
        simp only [Set.mem_sdiff]
        exact ⟨fun hx => hx.1, fun hx =>
          ⟨hx, fun hxk => Set.eq_empty_iff_forall_notMem.mp hInterEmpty x ⟨hx, hxk⟩⟩⟩
      rw [ite_eq_left h1]
      refine ⟨Or.inl rfl, hBW, iff_of_true hInterEmpty rfl, ?_, Set.empty_union _,
        Set.empty_inter _⟩
      rw [hdiffEq]; exact hAB
    · by_cases h2 : emptyDiffDec P hDiff (Nat.pair n k) = 1
      · have hDiffEmpty : P.X n \ P.X k = ∅ :=
          (emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mp h2
        have hInterEq : P.X n ∩ P.X k = P.X n := by
          ext x
          simp only [Set.mem_inter_iff]
          refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
          by_contra hxk
          exact Set.eq_empty_iff_forall_notMem.mp hDiffEmpty x ⟨hx, hxk⟩
        rw [ite_eq_right h1, ite_eq_left h2]
        refine ⟨hBW, Or.inl rfl, ?_, iff_of_true hDiffEmpty rfl, Set.union_empty _,
          Set.inter_empty _⟩
        rw [hInterEq]; exact hAB
      · have h1' : P.X n ∩ P.X k ≠ ∅ :=
          fun he => h1 ((emptyInterDec.eq_one_iff P hpos hnomin n k).mpr he)
        have h2' : P.X n \ P.X k ≠ ∅ :=
          fun he => h2 ((emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mpr he)
        rw [ite_eq_right h1, ite_eq_right h2]
        exact ⟨Or.inr (Q.mem_X _), Or.inr (Q.mem_X _), iff_of_false h1' (hQne _),
          iff_of_false h2' (hQne _), B.union m, B.disjoint m⟩
  · unfold splitFromBisection
    rw [dite_eq_right h]
    exact splitChoice'_isSplitSpec W hWnomin hAB hBW Xn

end splitFromBisection
end ComputableBisection
end

section
open Domain.Recursive NeighborhoodSystem

/-- **`8.12(g)(3)`, `V`-as-prober half**: `splitX812f` also satisfies `SplitSpec'`, the mirror
image of `Exercise812eD.lean`'s `hxSplit812e`. The extra hypothesis it needs, `∀ j, UX j ≠ ∅`, is
immediate from `U_mem_UX`/`U.mem`'s own `X.Nonempty` conjunct (`Definition87.lean` line 96). -/
theorem hySplit812f : SplitSpec' U splitX812f :=
  ComputableBisection.splitFromBisection.isSplitSpec' VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed
    (fun j => (U_mem_UX j).2.1.ne_empty)
end

namespace Uunion
open Domain.Recursive NeighborhoodSystem

section
/-- **`Uunion n m` genuinely indexes `UX n ∪ UX m`** — mirrors `Udiff.spec`'s shape exactly, but the
hypothesis is never used (the union is already unconditionally genuine, `U_union_mem`): the raw
`appendListCode` output is already a genuine `U`-neighbourhood, so re-canonicalizing it (`canonCode`'s
own lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem spec {n m : ℕ} (_ : ∃ k, UX k = UX n ∪ UX m) : UX (Uunion n m) = UX n ∪ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Uunion n m))) := by
    rw [Uunion.eq_union]; exact U_union_UX_mem n m
  show presentedIntervals (decodeQPairList (canonCode (Uunion n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Uunion.eq_union]
end

end Uunion
open Domain.Recursive NeighborhoodSystem

section
/-- **`8.12(g)(3)`, `U`-as-prober half**: `splitX812e` also satisfies `SplitSpec'` — completing the
concrete-construction half of `8.12(g)(3)` left open by `Exercise812e.lean`'s generic
`splitFromBisection.isSplitSpec'`. The extra hypothesis it needs, `∀ j, VX j ≠ ∅`, is immediate:
every `VX j` is `V.mem`-genuine (`VComputablePresentation.mem_X`) and `V.mem` structurally excludes
`∅` (`V.mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty`, `Exercise812.lean` line 199). -/
theorem hxSplit812e : SplitSpec' V splitX812e :=
  ComputableBisection.splitFromBisection.isSplitSpec' UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed (fun j => (VX_nonempty j).ne_empty)
end

section
/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `𝒰` — via `U_surj_UX` on
`U_union_UX_mem` (mirroring `U_diff_iff_nonempty`'s use of `U_surj_UX`, but unconditional). -/
theorem U_union_exists (n m : ℕ) : ∃ k, UX k = UX n ∪ UX m := U_surj_UX (U_union_UX_mem n m)
end

section
/-- **7.1(i)-for-`∪`, for `𝒰`**: trivially recursively decidable (the always-`1` constant), since
`U_union_exists` shows the underlying predicate is unconditionally `True`. -/
theorem U_union_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n ∪ UX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (U_union_exists t.unpair.1 t.unpair.2) rfl⟩
end

section
/-- **`U` has a computable `∪`.** -/
def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion.primrec
  unionIdx_spec := Uunion.spec
  union_computable := U_union_computable
end

namespace levelSet
open Domain.Recursive NeighborhoodSystem

section
/-- **Computable version of `levelSet.union_same_level` at differing levels** — the bitwise-`OR`
analogue of `levelSet.myInter`, mirroring its proof verbatim with `myLor`/`Nat.testBit_or` in place
of `myLand`/`Nat.testBit_and`. -/
theorem myUnion (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∪ levelSet k2 m2
      = levelSet (max k1 k2) (myLor (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet.union_same_level, myLor_eq_lor]
end

section
/-- **`VunionRaw` realizes `VX n ∪ VX m`** at the `levelSet` level (unconditionally). -/
theorem VunionRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.2 = VX n ∪ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VunionRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myUnion (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm
end

end levelSet
namespace Vunion
open Domain.Recursive NeighborhoodSystem

section
/-- **`Vunion n m` genuinely indexes `VX n ∪ VX m`**, unconditionally — `VunionRaw n m` is already
non-empty (both `VX n`, `VX m` are non-empty, `VX_nonempty`, and a union of a non-empty set with
anything is non-empty), so `canonIdx` is a no-op on it (`canonIdx.eq_self_of_nonempty`), mirroring
`Vinter_spec`'s shape but with the hypothesis discharged internally rather than assumed. -/
theorem spec (n m : ℕ) : VX (Vunion n m) = VX n ∪ VX m := by
  have hne : (levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VunionRaw]; exact (VX_nonempty n).mono Set.subset_union_left
  unfold Vunion
  rw [VX_canonIdx]
  show levelSet (canonIdx (VunionRaw n m)).unpair.1 (canonIdx (VunionRaw n m)).unpair.2 = VX n ∪ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VunionRaw]
end

section
/-- `Vunion.spec`, repackaged to accept (and discard) `IsComputableUnion`'s hypothesis. -/
theorem spec' {n m : ℕ} (_ : ∃ k, VX k = VX n ∪ VX m) : VX (Vunion n m) = VX n ∪ VX m :=
  Vunion.spec n m
end

end Vunion
open Domain.Recursive NeighborhoodSystem

section
/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `V` — witnessed directly by `Vunion`. -/
theorem V_union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion.spec n m⟩
end

section
/-- **7.1(i)-for-`∪`, for `V`**: trivially recursively decidable (the always-`1` constant). -/
theorem V_union_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n ∪ VX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (V_union_exists t.unpair.1 t.unpair.2) rfl⟩
end

namespace levelSet
open Domain.Recursive NeighborhoodSystem

section
/-- `levelSet 0 0 = ∅`: at level `0`, mask `0` has no set bits. -/
theorem zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]
end

end levelSet
open Domain.Recursive NeighborhoodSystem

section
/-- `hY0`: index `0` presents `V`'s master neighbourhood. `Nat.unpair 0 = (0, 0)` and
`levelSet 0 0 = ∅`, so `canonIdx 0` falls back to `VmasterIdx = Nat.pair 0 1`
(`canonIdx.eq_master_of_empty`), whose `VX`-image is `V.master` (`VX_VmasterIdx`). -/
theorem VX_zero : VX 0 = V.master := by
  have hc0 : canonIdx 0 = VmasterIdx :=
    canonIdx.eq_master_of_empty (by rw [Nat.unpair_zero]; exact levelSet.zero_zero)
  rw [← VX_canonIdx 0, hc0]
  exact VX_VmasterIdx
end

section
set_option linter.unusedVariables false

theorem example_812_e_d : @DomainTheory.NeighbourhoodSystems.SplitSpec' Rat Nat DomainTheory.NeighbourhoodSystems.V
  DomainTheory.NeighbourhoodSystems.splitX812e :=
  @DomainTheory.NeighbourhoodSystems.hxSplit812e

theorem example_812_f : @DomainTheory.NeighbourhoodSystems.SplitSpec' Nat Rat DomainTheory.NeighbourhoodSystems.U
  DomainTheory.NeighbourhoodSystems.splitX812f :=
  @DomainTheory.NeighbourhoodSystems.hySplit812f

theorem example_812_g1a : @Eq (Set Rat) (DomainTheory.NeighbourhoodSystems.UX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Rat DomainTheory.NeighbourhoodSystems.U) :=
  DomainTheory.NeighbourhoodSystems.UX_zero

theorem example_812_g1b : @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Nat DomainTheory.NeighbourhoodSystems.V) :=
  DomainTheory.NeighbourhoodSystems.VX_zero

theorem example_812_g2 : ∀ {n m : Nat},
  (∃ (k : Nat),
      @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX k)
        (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
          (DomainTheory.NeighbourhoodSystems.VX m))) →
    @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (DomainTheory.NeighbourhoodSystems.Vunion n m))
      (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
        (DomainTheory.NeighbourhoodSystems.VX m)) :=
  @DomainTheory.NeighbourhoodSystems.Vunion.spec'

end

namespace primrec
open Domain.Recursive NeighborhoodSystem

section
theorem VunionRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VunionRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1) := primrec.canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2) := primrec.canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) :=
    (primrec.myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) :=
    (primrec.myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hlor : Nat.Primrec (fun t : ℕ => myLor
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myLor.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hlor).of_eq fun _ => rfl
end

section
theorem Vunion : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vunion t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VunionRaw).of_eq fun _ => rfl
end

end primrec
section
open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `∪`.** -/
def V_isComputableUnion : IsComputableUnion VComputablePresentation where
  unionIdx := Vunion
  unionIdx_primrec := primrec.Vunion
  unionIdx_spec := Vunion.spec'
  union_computable := V_union_computable
end

section
open Domain.Recursive NeighborhoodSystem Exercise718

/-- **Exercise 8.12, completed in full**: `U` and `V` are effectively isomorphic
neighbourhood systems. -/
noncomputable def effectiveIso812_UV : EffectiveIso UComputablePresentation VComputablePresentation :=
  effectiveIso812d UComputablePresentation VComputablePresentation U_isComputableDiff
    V_isComputableDiff splitX812e isComputableSplit.«812e» splitX812f isComputableSplit.«812f»
    U_isPositive U_diffClosed U_noMinimal hxSplit812e V_isPositive V_diffClosed V_noMinimal
    hySplit812f U_master_nonempty V_master_nonempty U_isComputableUnion V_isComputableUnion UX_zero
    VX_zero
end

section
open NeighborhoodSystem

/-- The Boolean subalgebra of `Set ℕ` generated by a family `g` of "generators": the smallest
family containing every `g i` and `Set.univ`, closed under `∩`, `∪`, and complement. (`∅` is
derivable: `univ.compl`.) -/
inductive GeneratedBy {α : Type*} (g : ℕ → Set α) : Set α → Prop
  | of (i : ℕ) : GeneratedBy g (g i)
  | univ : GeneratedBy g Set.univ
  | inter {X Y} : GeneratedBy g X → GeneratedBy g Y → GeneratedBy g (X ∩ Y)
  | union {X Y} : GeneratedBy g X → GeneratedBy g Y → GeneratedBy g (X ∪ Y)
  | compl {X} : GeneratedBy g X → GeneratedBy g Xᶜ

/-- Build a natural number with a prescribed (finite) set of bits set — the "witness" constructor
used both for `generator`'s `levelSet` realization and for the complement/independence proofs
below. -/
def bitmaskOf (s : Finset ℕ) : ℕ := ∑ j ∈ s, 2 ^ j

/-- **`(∑ j ∈ s, 2^j).testBit i ↔ i ∈ s`.** The general "read off a prescribed finite bit pattern"
fact behind `upsample` (`Exercise812.lean`) — isolated here for reuse. -/
theorem testBit_sum_two_pow {s : Finset ℕ} {i : ℕ} : (∑ j ∈ s, 2 ^ j).testBit i ↔ i ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

@[simp] theorem testBit_bitmaskOf {s : Finset ℕ} {i : ℕ} : (bitmaskOf s).testBit i ↔ i ∈ s :=
  testBit_sum_two_pow

/-- The **`i`-th generator**: `{n | n.testBit i}`, the set of naturals whose `i`-th binary digit is
`1`. These are Scott's `ℵ₀` propositional variables, realized concretely. -/
def generator (i : ℕ) : Set ℕ := {n : ℕ | n.testBit i = true}

@[simp] theorem mem_generator {i n : ℕ} : n ∈ generator i ↔ n.testBit i = true := Iff.rfl

end
end DomainTheory.NeighbourhoodSystems
end
