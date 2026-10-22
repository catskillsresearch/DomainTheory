/-ai
Theorem 8.5, from a finitary projection to Scott's step-closure formula, states that if a is a finitary projection, then a neighbourhood Y belongs to a of an element x exactly when Y belongs to E and some neighbourhood X of x is contained in Y and is related to itself by a.

The proof unpacks the finitary projection into a retraction, a projection inequality, and an order isomorphism from the fixed set of a to the elements of a neighbourhood system F. If Y belongs to a of x, idempotence of the element map makes w equal to a of x fixed, and the section of the isomorphism sends the image of that fixed element back to w. Membership of Y in that section image is membership of Y in the section of some principal neighbourhood of the image. The retraction and the projection inequality turn the inverse image of that principal into a principal neighbourhood of some X in E, so Y belongs to E and X is contained in Y. The inverse image is fixed by a, so a relates X to itself. The principal of X lies below w because the principal in F lies below the image and the inverse of the isomorphism is monotone, and w lies below x because a lies below the identity, so x contains X. In the other direction, a self-related neighbourhood of x contained in a neighbourhood Y puts Y in a of x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.mem_of_exists_rel_self
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.toElementMap_idem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.exists_principal_eq_of_isRetraction_le_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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
theorem formula_of_isFinitaryProjection {a : ApproximableMap E E} (h : FinitaryProjection a) :
    ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X := by
  obtain ⟨⟨ha_ret, ha_proj⟩, β, F, ⟨e⟩⟩ := h.out
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
end DomainTheory.NeighbourhoodSystems
