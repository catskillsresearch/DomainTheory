module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD_rel_self_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piDType
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDType_monotone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_piDApplyu27

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap






















































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

end DomainTheory.NeighbourhoodSystems
