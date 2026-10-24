module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_19
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Hom.Basic
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

section
/- concordance: source L913 EXERCISE 2.20 powerset of the integers -/
/-- **Exercise 2.20 — the powerset system `𝒫`.** Tokens `ℕ`; the neighbourhoods are the cofinite
sets, closed under finite intersection (`(X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ`). -/
def powerSet : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]; exact hX.union hY
  sub_master := fun _ => Set.subset_univ _
end

section
@[simp] theorem mem_powerSet {X : Set ℕ} : powerSet.mem X ↔ Xᶜ.Finite := Iff.rfl
end

section
@[simp] theorem powerSet_master : powerSet.master = (Set.univ : Set ℕ) := rfl
end

section
/-- The complement of a singleton is a neighbourhood (it represents the finite element `{n}`). -/
theorem mem_compl_singleton (n : ℕ) : powerSet.mem ({n}ᶜ) := by
  rw [mem_powerSet, compl_compl]; exact Set.finite_singleton n
end

section
/-- Cofinite sets are closed under intersection (witness-free form). -/
theorem powerSet_inter_mem {A B : Set ℕ} (hA : powerSet.mem A) (hB : powerSet.mem B) :
    powerSet.mem (A ∩ B) := by
  rw [mem_powerSet, Set.compl_inter]; exact hA.union hB
end

section
/-- The subset of `ℕ` represented by an element: `n ∈ toSet x ↔ {n}ᶜ ∈ x`. -/
def toSet (x : powerSet.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}
end

section
@[simp] theorem mem_toSet {x : powerSet.Element} {n : ℕ} : n ∈ toSet x ↔ x.mem ({n}ᶜ) := Iff.rfl
end

section
/-- **Filters are determined on cofinite sets by their singleton-complements.** For cofinite `Z`,
`Z ∈ x ↔ ∀ n ∈ Zᶜ, {n}ᶜ ∈ x` (since `Z = ⋂_{n ∈ Zᶜ} {n}ᶜ`, a *finite* intersection). -/
theorem mem_compl_of_finite (x : powerSet.Element) {t : Set ℕ} (ht : t.Finite)
    (h : ∀ n ∈ t, x.mem ({n}ᶜ)) : x.mem (tᶜ) := by
  revert h
  induction t, ht using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ha _hsfin ih =>
    intro h
    have hcompl : (insert a s)ᶜ = ({a}ᶜ) ∩ (sᶜ) := by rw [Set.insert_eq, Set.compl_union]
    rw [hcompl]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))
end

section
/-- The filter of a subset `S ⊆ ℕ`: the cofinite `Z` with `Zᶜ ⊆ S`. -/
def ofSet (S : Set ℕ) : powerSet.Element where
  mem Z := powerSet.mem Z ∧ Zᶜ ⊆ S
  sub h := h.1
  master_mem := ⟨powerSet.master_mem, by rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset S⟩
  inter_mem := by
    rintro Z W ⟨hZ, hZS⟩ ⟨hW, hWS⟩
    refine ⟨powerSet_inter_mem hZ hW, ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hZS hWS
  up_mem := by
    rintro Z W ⟨hZ, hZS⟩ hW hZW
    exact ⟨hW, (Set.compl_subset_compl.mpr hZW).trans hZS⟩
end

section
/-- `ofSet` is monotone in the set. -/
theorem ofSet_mono {S S' : Set ℕ} (h : S ⊆ S') : ofSet S ≤ ofSet S' :=
  fun _ hZ => ⟨hZ.1, hZ.2.trans h⟩
end

section
theorem ofSet_toSet (x : powerSet.Element) : ofSet (toSet x) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hZsub⟩
    have hmem := mem_compl_of_finite x hZ (fun n hn => hZsub hn)
    rwa [compl_compl] at hmem
  · intro hZ
    refine ⟨x.sub hZ, ?_⟩
    intro n hn
    rw [mem_toSet]
    exact x.up_mem hZ (mem_compl_singleton n) (Set.subset_compl_singleton_iff.mpr hn)
end

section
/-- `S − 1 = {n ∣ n + 1 ∈ S}`. -/
def predSet (S : Set ℕ) : Set ℕ := {n | n + 1 ∈ S}
end

section
@[simp] theorem mem_predSet {S : Set ℕ} {n : ℕ} : n ∈ predSet S ↔ n + 1 ∈ S := Iff.rfl
end

section
/-- **Exercise 2.20 — `x ∩ y` is approximable (two variables).** `X, Y f Z ↔ X ∪ Y ⊆ Z`
(`(Xᶜ ∩ Yᶜ)ᶜ = X ∪ Y`). -/
def interMap₂ : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∪ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem,
    Set.union_subset (Set.subset_univ _) (Set.subset_univ _)⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.union_subset_union hX'X hY'Y).trans (hsub.trans hZZ')⟩
end

section
theorem predSet_mono {S T : Set ℕ} (h : S ⊆ T) : predSet S ⊆ predSet T := fun _ hn => h hn
end

section
/-- **Exercise 2.20 — `x − 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ − 1)`. -/
def predMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ predSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (predSet_mono (Set.compl_subset_compl.mpr hX'X)))
end

section
/-- `S + 1 = {n + 1 ∣ n ∈ S}`. -/
def succSet (S : Set ℕ) : Set ℕ := (· + 1) '' S
end

section
theorem succSet_mono {S T : Set ℕ} (h : S ⊆ T) : succSet S ⊆ succSet T := Set.image_mono h
end

section
/-- **Exercise 2.20 — `x + 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ + 1)`. -/
def succMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ succSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (succSet_mono (Set.compl_subset_compl.mpr hX'X)))
end

section
theorem toSet_ofSet (S : Set ℕ) : toSet (ofSet S) = S := by
  ext n
  simp only [mem_toSet]
  constructor
  · rintro ⟨_, hsub⟩
    rw [compl_compl] at hsub
    exact hsub (Set.mem_singleton n)
  · intro hn
    exact ⟨mem_compl_singleton n, by rw [compl_compl]; exact Set.singleton_subset_iff.mpr hn⟩
end

section
/-- **Exercise 2.20 — the identification `|𝒫| ≅ (Set ℕ, ⊆)`.** -/
def equivSetNat : powerSet.Element ≃o Set ℕ where
  toFun := toSet
  invFun := ofSet
  left_inv := ofSet_toSet
  right_inv := toSet_ofSet
  map_rel_iff' := by
    intro x y
    show toSet x ≤ toSet y ↔ x ≤ y
    constructor
    · intro h
      have hmono := ofSet_mono h
      rwa [ofSet_toSet, ofSet_toSet] at hmono
    · intro h n hn
      exact h _ hn
end

section
/-- **Exercise 2.20 — `x ∪ y` is approximable (two variables).** `X, Y f Z ↔ X ∩ Y ⊆ Z`
(`(Xᶜ ∪ Yᶜ)ᶜ = X ∩ Y`). -/
def unionMap : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem, Set.inter_subset_left⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.inter_subset_inter hX'X hY'Y).trans (hsub.trans hZZ')⟩
end

section
theorem toSet_interMap₂ (x y : powerSet.Element) :
    toSet (interMap₂.toElementMap₂ x y) = toSet x ∩ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_inter_iff]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    have hkX : k ∉ X := fun h => (hsub (Or.inl h)) rfl
    have hkY : k ∉ Y := fun h => (hsub (Or.inr h)) rfl
    exact ⟨x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX),
      y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)⟩
  · rintro ⟨hkx, hky⟩
    exact ⟨{k}ᶜ, {k}ᶜ, hkx, hky, mem_compl_singleton k, mem_compl_singleton k,
      mem_compl_singleton k, Set.union_subset subset_rfl subset_rfl⟩
end

section
theorem toSet_predMap (x : powerSet.Element) :
    toSet (predMap.toElementMap x) = predSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap, mem_predSet]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    have hk : k + 1 ∈ Xᶜ := hsub (Set.mem_singleton k)
    exact x.up_mem hxX (mem_compl_singleton (k + 1)) (Set.subset_compl_singleton_iff.mpr hk)
  · intro hk
    refine ⟨{k + 1}ᶜ, hk, mem_compl_singleton (k + 1), mem_compl_singleton k, ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    rw [mem_predSet, compl_compl]
    exact Set.mem_singleton (a + 1)
end

section
theorem toSet_succMap (x : powerSet.Element) :
    toSet (succMap.toElementMap x) = succSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    obtain ⟨m, hm, rfl⟩ := hsub (Set.mem_singleton k)
    exact ⟨m, x.up_mem hxX (mem_compl_singleton m) (Set.subset_compl_singleton_iff.mpr hm), rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨{m}ᶜ, hm, mem_compl_singleton m, mem_compl_singleton (m + 1), ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    exact ⟨m, by rw [compl_compl]; exact Set.mem_singleton m, rfl⟩
end

section
theorem toSet_unionMap (x y : powerSet.Element) :
    toSet (unionMap.toElementMap₂ x y) = toSet x ∪ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_union]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    by_cases hkX : k ∈ X
    · refine Or.inr ?_
      have hkY : k ∉ Y := fun hkY => (hsub ⟨hkX, hkY⟩) rfl
      exact y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)
    · exact Or.inl (x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX))
  · rintro (hkx | hky)
    · exact ⟨{k}ᶜ, Set.univ, hkx, y.master_mem, mem_compl_singleton k, powerSet.master_mem,
        mem_compl_singleton k, Set.inter_subset_left⟩
    · exact ⟨Set.univ, {k}ᶜ, x.master_mem, hky, powerSet.master_mem, mem_compl_singleton k,
        mem_compl_singleton k, Set.inter_subset_right⟩
end

section
set_option linter.unusedVariables false

theorem example_220 : ∀
  (x y :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
      DomainTheory.NeighbourhoodSystems.Exercise220.powerSet),
  @Eq (Set Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise220.toSet
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.toElementMap₂ Nat Nat Nat
        DomainTheory.NeighbourhoodSystems.Exercise220.powerSet DomainTheory.NeighbourhoodSystems.Exercise220.powerSet
        DomainTheory.NeighbourhoodSystems.Exercise220.powerSet DomainTheory.NeighbourhoodSystems.Exercise220.unionMap x
        y))
    (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.Exercise220.toSet x)
      (DomainTheory.NeighbourhoodSystems.Exercise220.toSet y)) :=
  DomainTheory.NeighbourhoodSystems.Exercise220.toSet_unionMap
end

end DomainTheory.NeighbourhoodSystems.Exercise220
