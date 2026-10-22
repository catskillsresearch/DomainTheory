module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.IsCompactElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.sectionMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.BasicInst8

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}


/-- A neighbourhood `Z` witnessing `y`'s membership is always a *lower bound* on `y`: `↑Z ⊑ y`.
The general form of `Basic.lean`'s remark that `⊥ = ↑Δ` is least: any witnessed `↑Z` sits below
the element it witnesses. -/
theorem principal_le_of_mem {y : V.Element} {Z : Set γ} (hZ : y.mem Z) :
    V.principal (y.sub hZ) ≤ y :=
  fun _ ⟨hW, hZW⟩ => y.up_mem hZ hW hZW

theorem principalFamily_directed (x : V.Element) :
    ∀ i j : {X : Set γ // x.mem X}, ∃ k : {X : Set γ // x.mem X},
      V.principal (x.sub i.2) ≤ V.principal (x.sub k.2) ∧
        V.principal (x.sub j.2) ≤ V.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

/-- **Algebraicity.** Every element `x` is the directed union of its own principal
("finite"/compact) approximants: `x = ⋃ {↑X ∣ X ∈ x}`, now literally as an `iSupDirected`
(rather than `eq_iUnion_principal`'s membership-only form). -/
theorem eq_iSupDirected_principal (x : V.Element) :
    x = iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ


end Algebraic

section HardDirection

variable {a : ApproximableMap E E}

/-- The sup of a directed family of `a`-fixed elements is again `a`-fixed: `a` is continuous
(`toElementMap_iSupDirected`), so `a` applied to the sup is the sup of `a` applied pointwise, which
is the original family by `hfix`. -/
theorem toElementMap_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i) :
    a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir := by
  rw [toElementMap_iSupDirected]
  apply Element.ext
  intro Z
  rw [mem_iSupDirected, mem_iSupDirected]
  simp_rw [hfix]

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)


@[simp] theorem toElementMap_sectionMap_principal {X : Set β} (hX : F.mem X) :
    (sectionMap e).toElementMap (F.principal hX) = (e.symm (F.principal hX)).1 :=
  toElementMap_ofMono_principal _ _ X hX

/-- **Claim′.** `i` realizes `e.symm` at *every* element of `F`, not just the principal ones:
`i(w') = e.symm(w')` (as `E`-elements).

`≤`: `i(w') = ⋃_{X ∈ w'} i(↑X) = ⋃_{X ∈ w'} e.symm(↑X)`, and each `e.symm(↑X) ≤ e.symm(w')` by
`principal_le_of_mem` and monotonicity of `e.symm`.

`≥`: the family `c(X) := e.symm(↑X)` (`X ∈ w'`) is directed with sup exactly `i(w')` (`hS_eq`
below, "for free" from the membership formula), hence `a`-fixed (`toElementMap_iSupDirected_fixed`).
Algebraicity of `w'` in `F` reduces `w' ≤ e(i(w'))` to checking `↑X ≤ e(i(w'))` for each `X ∈ w'`,
which (applying `e.symm`) is exactly `c(X) ≤ i(w')` — true since `i(w')` is the sup of the `c`
family. -/
theorem toElementMap_sectionMap (w' : F.Element) :
    (sectionMap e).toElementMap w' = (e.symm w').1 := by
  have hdirC : ∀ i j : {X : Set β // w'.mem X}, ∃ k : {X : Set β // w'.mem X},
      (e.symm (F.principal (w'.sub i.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 ∧
        (e.symm (F.principal (w'.sub j.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 :=
    fun i j => ⟨⟨i.1 ∩ j.1, w'.inter_mem i.2 j.2⟩,
      e.symm.monotone ((F.principal_le_iff (w'.sub i.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_left),
      e.symm.monotone ((F.principal_le_iff (w'.sub j.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_right)⟩
  have hS_eq : (sectionMap e).toElementMap w' =
      iSupDirected (fun i : {X : Set β // w'.mem X} => (e.symm (F.principal (w'.sub i.2))).1)
        hdirC := by
    apply Element.ext
    intro Z
    rw [toElementMap_mem_iff_principal, mem_iSupDirected]
    constructor
    · rintro ⟨X, hX, hZ⟩; rw [toElementMap_sectionMap_principal] at hZ; exact ⟨⟨X, hX⟩, hZ⟩
    · rintro ⟨⟨X, hX⟩, hZ⟩; exact ⟨X, hX, by rwa [toElementMap_sectionMap_principal]⟩
  have hfixC : ∀ i : {X : Set β // w'.mem X},
      a.toElementMap (e.symm (F.principal (w'.sub i.2))).1 =
        (e.symm (F.principal (w'.sub i.2))).1 :=
    fun i => (e.symm (F.principal (w'.sub i.2))).2
  apply le_antisymm
  · rw [hS_eq]
    apply iSupDirected_le
    intro i
    exact e.symm.monotone (principal_le_of_mem i.2)
  · have hSfix : a.toElementMap ((sectionMap e).toElementMap w') =
        (sectionMap e).toElementMap w' := by
      rw [hS_eq]; exact toElementMap_iSupDirected_fixed _ hdirC hfixC
    have key : w' ≤ e ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
      refine le_trans (le_of_eq (eq_iSupDirected_principal w'))
        (iSupDirected_le _ (principalFamily_directed w') ?_)
      intro i
      have : e.symm (F.principal (w'.sub i.2)) ≤ ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
        show (e.symm (F.principal (w'.sub i.2))).1 ≤ (sectionMap e).toElementMap w'
        rw [hS_eq]
        exact le_iSupDirected _ hdirC i
      have := e.monotone this
      rwa [e.apply_symm_apply] at this
    have := e.symm.monotone key
    rwa [e.symm_apply_apply] at this
end HardDirection
end DomainTheory.NeighbourhoodSystems
