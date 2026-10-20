/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem85.Basic
import DomainTheory.Neighborhood.Theorem85.mem_of_exists_rel_self
import DomainTheory.Neighborhood.Theorem85.toElementMap_idem
import DomainTheory.Neighborhood.Theorem85.exists_principal_eq_of_isRetraction_le_idMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}






section HardDirection

variable {a : ApproximableMap E E}



variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)




/-- **Theorem 8.5, `(i) ⟹ (ii)` (Scott 1981, PRG-19), assembled.** If `a` is a finitary projection,
it satisfies Scott's step-closure formula.

Given `Y ∈ a(x)`: since `a` is idempotent, `w := a(x)` is itself `a`-fixed, and `e ⟨w, _⟩ : F.Element`
decomposes (Exercise 2.9, via `sectionMap`'s `Claim′`) as a union of `sectionMap e`'s values on
`F`-principals `↑W` for `W ∈ e ⟨w, _⟩`; picking the `W` witnessing `Y`, compactness reflection turns
`(e.symm ↑W).1` into a genuine `E`-principal `↑X`. `X ⊆ Y` and `X a X` both come from `X`'s defining
equation `a(↑X) = ↑X` (inherited from `FixSet`); `x.mem X` comes from `↑X ≤ w = a(x) ≤ x` (the last
step using `a ≤ I_E`). -/
theorem formula_of_isFinitaryProjection {a : ApproximableMap E E} (h : IsFinitaryProjection a) :
    ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X := by
  obtain ⟨⟨ha_ret, ha_proj⟩, β, F, ⟨e⟩⟩ := h
  intro x Y
  constructor
  · intro hY
    have hw : a.toElementMap (a.toElementMap x) = a.toElementMap x := toElementMap_idem ha_ret x
    set w : E.Element := a.toElementMap x with hw_def
    have hYw : w.mem Y := hY
    have hclaim : (sectionMap e).toElementMap (e ⟨w, hw⟩) = w := by
      rw [toElementMap_sectionMap e (e ⟨w, hw⟩), e.symm_apply_apply]
    have hYsec : ((sectionMap e).toElementMap (e ⟨w, hw⟩)).mem Y := by rw [hclaim]; exact hYw
    obtain ⟨W, hW, hYW⟩ := (toElementMap_mem_iff_principal (sectionMap e) (e ⟨w, hw⟩)).mp hYsec
    rw [toElementMap_sectionMap_principal] at hYW
    obtain ⟨X, hX, hXeq⟩ :=
      exists_principal_eq_of_isRetraction_le_idMap e ha_ret ha_proj ((e ⟨w, hw⟩).sub hW)
    rw [hXeq] at hYW
    obtain ⟨hYE, hXY⟩ := (E.mem_principal hX).mp hYW
    have hfixX : a.toElementMap (E.principal hX) = E.principal hX := by
      rw [← hXeq]; exact (e.symm (F.principal ((e ⟨w, hw⟩).sub hW))).2
    have haXX : a.rel X X := (a.rel_iff_mem_principal hX).mpr (by
      rw [hfixX]; exact (E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)
    have hprincipal_le_w : E.principal hX ≤ w := by
      have h1 : F.principal ((e ⟨w, hw⟩).sub hW) ≤ e ⟨w, hw⟩ :=
        principal_le_of_mem hW
      have h2 : e.symm (F.principal ((e ⟨w, hw⟩).sub hW)) ≤ e.symm (e ⟨w, hw⟩) :=
        e.symm.monotone h1
      have h3 : (e.symm (F.principal ((e ⟨w, hw⟩).sub hW))).1 ≤ w := by
        have := h2
        rwa [e.symm_apply_apply] at this
      rwa [hXeq] at h3
    have hw_le_x : w ≤ x := by
      have := (le_iff_toElementMap_le.mp ha_proj) x
      rwa [toElementMap_idMap] at this
    have hXx : x.mem X := hprincipal_le_w.trans hw_le_x X ((E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)
    exact ⟨hYE, X, hXx, hXY, haXX⟩
  · rintro ⟨hYE, X, hXx, hXY, hXaX⟩
    exact mem_of_exists_rel_self x hYE hXx hXY hXaX

end HardDirection
end DomainTheory.Neighborhood
