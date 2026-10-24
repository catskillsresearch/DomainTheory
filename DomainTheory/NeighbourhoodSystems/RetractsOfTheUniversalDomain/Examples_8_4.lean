module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
/- concordance: source L4807 EXAMPLES 8.4 check, fade, and smash -/
/-- **Example 8.4's two-point system `O = {{0},{0,1}}`.** Tokens `Δ = {0,1} : Fin 2`; the only
neighbourhoods are `{0}` (most informative) and `{0,1}` (the master, least informative). -/
def O : NeighborhoodSystem (Fin 2) where
  mem X := X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2))
  master := ({0, 1} : Set (Fin 2))
  master_nonempty := ⟨0, by simp⟩
  master_mem := Or.inr rfl
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · exact Or.inl (Set.inter_self _)
    · exact Or.inl (Set.inter_eq_left.mpr fin2_zero_subset_zero_one)
    · exact Or.inl (Set.inter_eq_right.mpr fin2_zero_subset_zero_one)
    · exact Or.inr (Set.inter_self _)
  sub_master := by
    rintro X (rfl | rfl)
    · exact fin2_zero_subset_zero_one
    · exact subset_rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem O_master_eq : O.master = ({0, 1} : Set (Fin 2)) := rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂

@[simp] theorem O_mem_iff {X : Set (Fin 2)} :
    O.mem X ↔ X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2)) := Iff.rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem O_mem_zero : O.mem ({0} : Set (Fin 2)) := Or.inl rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂

/-- `O`'s top element `⊤ = ↑{0}` (the more informative of the two elements; `O.bot = ↑{0,1}` is the
generic `NeighborhoodSystem.bot`). -/
def Otop : O.Element := O.principal O_mem_zero
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂

@[simp] theorem mem_Otop {Y : Set (Fin 2)} : Otop.mem Y ↔ O.mem Y ∧ ({0} : Set (Fin 2)) ⊆ Y :=
  Iff.rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- **Example 8.4's `check` combinator.** `X check Y ↔ Y = {0,1} ∨ X ≠ Δ_D`. -/
def check : ApproximableMap D O where
  rel X Y := D.mem X ∧ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ X ≠ D.master)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, O.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hY1⟩ ⟨-, hY', hY1'⟩
    refine ⟨hX, ?_, ?_⟩
    · rcases hY with rfl | rfl <;> rcases hY' with rfl | rfl
      · exact Or.inl (Set.inter_self _)
      · exact Or.inl (Set.inter_eq_left.mpr fin2_zero_subset_zero_one)
      · exact Or.inl (Set.inter_eq_right.mpr fin2_zero_subset_zero_one)
      · exact Or.inr (Set.inter_self _)
    · rcases hY1 with h1 | hXne
      · rcases hY1' with h1' | hXne'
        · left; rw [h1, h1']; simp
        · right; exact hXne'
      · right; exact hXne
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hY1⟩ hXX' hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    rcases hY1 with hYeq | hXne
    · left
      subst hYeq
      rcases hY' with rfl | rfl
      · exfalso
        have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
        have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := hYY' h1
        simp at h2
      · rfl
    · right
      intro hX'eq
      apply hXne
      exact Set.Subset.antisymm (D.sub_master hX) (hX'eq ▸ hXX')
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

@[simp] theorem check_rel {X : Set α} {Y : Set (Fin 2)} :
    (check : ApproximableMap D O).rel X Y ↔
      D.mem X ∧ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ X ≠ D.master) :=
  Iff.rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- A non-bottom element of `D` always has *some* member neighbourhood other than the master.
(Classical: uses `by_contra`/`push_neg`, an allowed `Prop`-level use of `Classical.choice`.) -/
theorem exists_mem_ne_master_of_ne_bot {y : D.Element} (hy : y ≠ D.bot) :
    ∃ Z, y.mem Z ∧ Z ≠ D.master := by
  by_contra hcon
  push Not at hcon
  apply hy
  apply Element.ext
  intro Z
  rw [mem_bot]
  exact ⟨fun hZ => hcon Z hZ, fun hZ => hZ ▸ y.master_mem⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- **Example 8.4's `fade` combinator, as a two-variable map.** `X, Y fade Z ↔ Z = Δ_D ∨ (X = {0}
∧ Y ⊆ Z)`: the master is always a safe output; `X = {0}` (the informative `O`-input) lets `Y` pass
straight through. -/
def fade₂ : ApproximableMap₂ O D D where
  rel X Y Z := O.mem X ∧ D.mem Y ∧ D.mem Z ∧ (Z = D.master ∨ (X = ({0} : Set (Fin 2)) ∧ Y ⊆ Z))
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨O.master_mem, D.master_mem, D.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hZ1⟩ ⟨-, -, hZ', hZ1'⟩
    refine ⟨hX, hY, ?_, ?_⟩
    · rcases hZ1 with rfl | ⟨-, hYZ⟩
      · rwa [Set.inter_eq_right.mpr (D.sub_master hZ')]
      · rcases hZ1' with rfl | ⟨-, hYZ'⟩
        · rwa [Set.inter_eq_left.mpr (D.sub_master hZ)]
        · exact D.inter_mem hZ hZ' hY (Set.subset_inter hYZ hYZ')
    · rcases hZ1 with rfl | ⟨hXeq, hYZ⟩
      · rcases hZ1' with rfl | ⟨hXeq', hYZ'⟩
        · left; exact Set.inter_self _
        · right
          refine ⟨hXeq', ?_⟩
          rw [Set.inter_eq_right.mpr (D.sub_master hZ')]
          exact hYZ'
      · right
        refine ⟨hXeq, ?_⟩
        rcases hZ1' with rfl | ⟨-, hYZ'⟩
        · rw [Set.inter_eq_left.mpr (D.sub_master hZ)]
          exact hYZ
        · exact Set.subset_inter hYZ hYZ'
  mono := by
    rintro X X' Y Y' Z Z' ⟨hX, hY, hZ, hZ1⟩ hXX' hYY' hZZ' hX' hY' hZ'
    refine ⟨hX', hY', hZ', ?_⟩
    rcases hZ1 with rfl | ⟨hXeq, hYZ⟩
    · left; exact Set.Subset.antisymm (D.sub_master hZ') hZZ'
    · have hX'eq : X' = ({0} : Set (Fin 2)) := by
        rcases hX' with rfl | rfl
        · rfl
        · exfalso
          have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
          have h2 : (1 : Fin 2) ∈ X := hXX' h1
          rw [hXeq] at h2
          simp at h2
      right
      exact ⟨hX'eq, hYY'.trans (hYZ.trans hZZ')⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- **Example 8.4's `fade` combinator**, packaged as a genuine `ApproximableMap (prod O D) D`
via the Theorem 3.5 bridge (`ofMap₂`). -/
def fade : ApproximableMap (prod O D) D := ofMap₂ fade₂
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

/-- **Example 8.4(a)'s retraction** `a(x) = fade(check(x), u)`. -/
def a : ApproximableMap D D := fade.comp (paired check (constMap D u))
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

/-- The `D`-element corresponding to `t : O.Element` under `a`'s formula: `Z ↦ Z = Δ_D ∨ (t ∋ {0}
∧ u ∋ Z)`. This is a genuine `Element` (filter), built with no case-split on `t`. -/
def fixOfO (t : O.Element) : D.Element where
  mem Z := D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ u.mem Z))
  sub h := h.1
  master_mem := ⟨D.master_mem, Or.inl rfl⟩
  inter_mem := by
    rintro Z Z' ⟨hZ, hZ1⟩ ⟨hZ', hZ1'⟩
    refine ⟨?_, ?_⟩
    · rcases hZ1 with rfl | ⟨-, huZ⟩
      · rwa [Set.inter_eq_right.mpr (D.sub_master hZ')]
      · rcases hZ1' with rfl | ⟨-, huZ'⟩
        · rwa [Set.inter_eq_left.mpr (D.sub_master hZ)]
        · exact u.sub (u.inter_mem huZ huZ')
    · rcases hZ1 with rfl | ⟨ht, huZ⟩
      · rcases hZ1' with rfl | ⟨ht', huZ'⟩
        · left; exact Set.inter_self _
        · right
          refine ⟨ht', ?_⟩
          rw [Set.inter_eq_right.mpr (D.sub_master hZ')]
          exact huZ'
      · right
        refine ⟨ht, ?_⟩
        rcases hZ1' with rfl | ⟨-, huZ'⟩
        · rw [Set.inter_eq_left.mpr (D.sub_master hZ)]
          exact huZ
        · exact u.inter_mem huZ huZ'
  up_mem := by
    rintro Z Z' ⟨hZ, hZ1⟩ hZ'D hZZ'
    refine ⟨hZ'D, ?_⟩
    rcases hZ1 with rfl | ⟨ht, huZ⟩
    · left; exact Set.Subset.antisymm (D.sub_master hZ'D) hZZ'
    · right; exact ⟨ht, u.up_mem huZ hZ'D hZZ'⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

@[simp] theorem mem_fixOfO {t : O.Element} {Z : Set α} :
    (fixOfO u t).mem Z ↔ D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ u.mem Z)) :=
  Iff.rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem O_le_iff {t t' : O.Element} :
    t ≤ t' ↔ (t.mem ({0} : Set (Fin 2)) → t'.mem ({0} : Set (Fin 2))) := by
  constructor
  · intro h; exact h _
  · intro h Y hY
    rcases O_mem_iff.mp (t.sub hY) with rfl | rfl
    · exact h hY
    · exact t'.master_mem
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem fixOfO_mono {t t' : O.Element} (h : t ≤ t') : fixOfO u t ≤ fixOfO u t' := by
  intro Z hZ
  rw [mem_fixOfO] at hZ ⊢
  obtain ⟨hZD, hZeq | ⟨ht0, huZ⟩⟩ := hZ
  · exact ⟨hZD, Or.inl hZeq⟩
  · exact ⟨hZD, Or.inr ⟨O_le_iff.mp h ht0, huZ⟩⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem fixOfO_ne_bot_iff (hu : u ≠ D.bot) {t : O.Element} :
    fixOfO u t ≠ D.bot ↔ t.mem ({0} : Set (Fin 2)) := by
  constructor
  · intro hne
    by_contra ht0
    apply hne
    apply Element.ext
    intro Z
    rw [mem_fixOfO, mem_bot]
    constructor
    · rintro ⟨-, rfl | ⟨ht0', -⟩⟩
      · rfl
      · exact absurd ht0' ht0
    · rintro rfl
      exact ⟨D.master_mem, Or.inl rfl⟩
  · intro ht0 hbot
    obtain ⟨Z, huZ, hZne⟩ := exists_mem_ne_master_of_ne_bot hu
    have : (fixOfO u t).mem Z := ⟨u.sub huZ, Or.inr ⟨ht0, huZ⟩⟩
    rw [hbot, mem_bot] at this
    exact hZne this
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- The closed form of `check`'s elementwise action: `check(x) ∋ Y ↔ Y ∈ O ∧ (Y = {0,1} ∨ x ≠ ⊥)`.
So `check(x) = ⊥_O` when `x = ⊥_D`, and `check(x) = ⊤_O` otherwise. -/
theorem mem_toElementMap_check {x : D.Element} {Y : Set (Fin 2)} :
    (check.toElementMap x).mem Y ↔ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ x ≠ D.bot) := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hXD, hYO, hcase⟩
    refine ⟨hYO, ?_⟩
    rcases hcase with h | hXne
    · exact Or.inl h
    · refine Or.inr fun hxbot => hXne ?_
      have hxX' : x.mem X := hxX
      rw [hxbot, mem_bot] at hxX'
      exact hxX'
  · rintro ⟨hYO, hYeq | hxne⟩
    · exact ⟨D.master, x.master_mem, D.master_mem, hYO, Or.inl hYeq⟩
    · obtain ⟨X, hxX, hXne⟩ := exists_mem_ne_master_of_ne_bot hxne
      exact ⟨X, hxX, x.sub hxX, hYO, Or.inr hXne⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem check_toElementMap_fixOfO (hu : u ≠ D.bot) (t : O.Element) :
    check.toElementMap (fixOfO u t) = t := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap_check, fixOfO_ne_bot_iff u hu]
  constructor
  · rintro ⟨hYO, hYeq | ht0⟩
    · rw [hYeq, ← O_master_eq]; exact t.master_mem
    · rcases hYO with rfl | rfl
      · exact ht0
      · rw [← O_master_eq]; exact t.master_mem
  · intro htY
    have hYO : O.mem Y := t.sub htY
    refine ⟨hYO, ?_⟩
    rcases O_mem_iff.mp hYO with rfl | rfl
    · exact Or.inr htY
    · exact Or.inl rfl
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- The closed form of `fade`'s elementwise action on a pair `⟨t, y⟩`: `fade(t,y) ∋ Z ↔ Z = Δ_D ∨
(t ∋ {0} ∧ y ∋ Z)`. -/
theorem mem_toElementMap₂_fade (t : O.Element) (y : D.Element) {Z : Set α} :
    (fade₂.toElementMap₂ t y).mem Z ↔
      D.mem Z ∧ (Z = D.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ y.mem Z)) := by
  rw [mem_toElementMap₂]
  constructor
  · rintro ⟨X, Y, htX, hyY, hXO, hYD, hZD, hcase⟩
    refine ⟨hZD, ?_⟩
    rcases hcase with h | ⟨hXeq, hYZ⟩
    · exact Or.inl h
    · exact Or.inr ⟨hXeq ▸ htX, y.up_mem hyY hZD hYZ⟩
  · rintro ⟨hZD, hZeq | ⟨ht0, hyZ⟩⟩
    · exact ⟨O.master, D.master, t.master_mem, y.master_mem, O.master_mem, D.master_mem, hZD,
        Or.inl hZeq⟩
    · exact ⟨({0} : Set (Fin 2)), Z, ht0, hyZ, O_mem_zero, hZD, hZD, Or.inr ⟨rfl, subset_rfl⟩⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}

/-- The two-variable elementwise bridge for a general `ApproximableMap₂`, specialized to a pair. -/
theorem toElementMap_ofMap₂_pair {β γ δ : Type*} {V₀ : NeighborhoodSystem β}
    {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ} (f₂ : ApproximableMap₂ V₀ V₁ V₂)
    (p : V₀.Element) (q : V₁.Element) :
    (ofMap₂ f₂).toElementMap (pair p q) = f₂.toElementMap₂ p q := by
  have h := toElementMap₂_toMap₂ (ofMap₂ f₂) p q
  rw [toMap₂_ofMap₂] at h
  exact h.symm
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem mem_toElementMap_a {x : D.Element} {Z : Set α} :
    ((a u).toElementMap x).mem Z ↔ D.mem Z ∧ (Z = D.master ∨ (x ≠ D.bot ∧ u.mem Z)) := by
  show ((fade.comp (paired check (constMap D u))).toElementMap x).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_constMap]
  show (fade.toElementMap (pair (check.toElementMap x) u)).mem Z ↔ _
  rw [show fade = ofMap₂ fade₂ from rfl, toElementMap_ofMap₂_pair, mem_toElementMap₂_fade,
    mem_toElementMap_check]
  constructor
  · rintro ⟨hZD, hZeq | ⟨⟨-, hcase⟩, huZ⟩⟩
    · exact ⟨hZD, Or.inl hZeq⟩
    · rcases hcase with hYeq | hxne
      · exact absurd hYeq fin2_zero_ne_zero_one
      · exact ⟨hZD, Or.inr ⟨hxne, huZ⟩⟩
  · rintro ⟨hZD, hZeq | ⟨hxne, huZ⟩⟩
    · exact ⟨hZD, Or.inl hZeq⟩
    · exact ⟨hZD, Or.inr ⟨⟨O_mem_zero, Or.inr hxne⟩, huZ⟩⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

/-- `fixOfO` and `check.toElementMap` intertwine `a` and the identity on `D`: applying `fixOfO`
after `check.toElementMap` recovers `a` itself. -/
theorem fixOfO_check_toElementMap (x : D.Element) :
    fixOfO u (check.toElementMap x) = (a u).toElementMap x := by
  apply Element.ext
  intro Z
  rw [mem_fixOfO, mem_toElementMap_a]
  have hcheck : (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
    rw [mem_toElementMap_check]
    constructor
    · rintro ⟨-, h | h⟩
      · exact absurd h fin2_zero_ne_zero_one
      · exact h
    · intro h; exact ⟨O_mem_zero, Or.inr h⟩
  rw [hcheck]
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem toElementMap_a_fixOfO (hu : u ≠ D.bot) (t : O.Element) :
    (a u).toElementMap (fixOfO u t) = fixOfO u t := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a, mem_fixOfO, fixOfO_ne_bot_iff u hu]
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

/-- **Example 8.4(a) (Scott 1981, PRG-19), packaged.** The range (fixed-point set) of `a` is
order-isomorphic to `O`. -/
def fixIso (hu : u ≠ D.bot) : O.Element ≃o {y : D.Element // (a u).toElementMap y = y} where
  toFun t := ⟨fixOfO u t, toElementMap_a_fixOfO u hu t⟩
  invFun y := check.toElementMap y.1
  left_inv t := check_toElementMap_fixOfO u hu t
  right_inv y := by
    apply Subtype.ext
    show fixOfO u (check.toElementMap y.1) = y.1
    rw [fixOfO_check_toElementMap, y.2]
  map_rel_iff' := by
    intro t t'
    show fixOfO u t ≤ fixOfO u t' ↔ t ≤ t'
    constructor
    · intro h
      have := toElementMap_mono check h
      rwa [check_toElementMap_fixOfO u hu, check_toElementMap_fixOfO u hu] at this
    · exact fixOfO_mono u
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem Otop_ne_Obot : Otop ≠ O.bot := by
  intro h
  have h1 : Otop.mem ({0} : Set (Fin 2)) := ⟨O_mem_zero, subset_rfl⟩
  rw [h, mem_bot, O_master_eq] at h1
  have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by rw [h1]; simp
  simp at h2
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem a_bot : (a u).toElementMap D.bot = D.bot := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a, mem_bot]
  exact ⟨fun ⟨_, h⟩ => h.resolve_right (fun h' => h'.1 rfl) |>.symm ▸ rfl,
    fun h => ⟨h ▸ D.master_mem, Or.inl h⟩⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

theorem a_of_ne_bot {x : D.Element} (hx : x ≠ D.bot) : (a u).toElementMap x = u := by
  apply Element.ext
  intro Z
  rw [mem_toElementMap_a]
  constructor
  · rintro ⟨-, hZeq | ⟨-, huZ⟩⟩
    · exact hZeq ▸ u.master_mem
    · exact huZ
  · intro huZ
    exact ⟨u.sub huZ, Or.inr ⟨hx, huZ⟩⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

/-- **Example 8.4(a) (Scott 1981, PRG-19).** `a` is a retraction. -/
theorem isRetraction_a (hu : u ≠ D.bot) : Retraction (a u) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  by_cases hx : x = D.bot
  · subst hx; rw [a_bot, a_bot]
  · rw [a_of_ne_bot u hx, a_of_ne_bot u hu]
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α : Type*} {D : NeighborhoodSystem α}
variable (u : D.Element) (hu : u ≠ D.bot)

/-- **Example 8.4(a) (Scott 1981, PRG-19), final statement.** If `D` is not trivial (`u ≠ ⊥`),
`a(x) = fade(check(x), u)` is a retraction on `D` whose range is isomorphic to `O = {{0},{0,1}}`. -/
theorem example84a (hu : u ≠ D.bot) :
    Retraction (a u) ∧ Nonempty (O.Element ≃o {y : D.Element // (a u).toElementMap y = y}) :=
  ⟨isRetraction_a u hu, ⟨fixIso u hu⟩⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- `check(x) ∋ {0} ↔ x ≠ ⊥`: the clean, non-set-theoretic form of `mem_toElementMap_check`. -/
theorem check_toElementMap_mem_zero_iff {x : D.Element} :
    (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
  rw [mem_toElementMap_check]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h fin2_zero_ne_zero_one
    · exact h
  · intro h; exact ⟨O_mem_zero, Or.inr h⟩
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- The closed form of `fade`'s elementwise action, generalized (via `mem_toElementMap₂_fade`) from
Example 8.4(a)'s ambient `D` to an arbitrary neighbourhood system `G`. -/
theorem mem_toElementMap_fade {γ : Type*} {G : NeighborhoodSystem γ} (t : O.Element) (w : G.Element)
    {Z : Set γ} :
    ((fade (D := G)).toElementMap (pair t w)).mem Z ↔
      G.mem Z ∧ (Z = G.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ w.mem Z)) := by
  rw [show (fade (D := G)) = ofMap₂ (fade₂ (D := G)) from rfl, toElementMap_ofMap₂_pair,
    mem_toElementMap₂_fade]
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

/-- `(prod D E).bot = ⟨⊥_D, ⊥_E⟩`. -/
theorem pair_bot_bot : pair (D.bot) (E.bot) = (prod D E).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨D.master, E.master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

@[simp] theorem prod_bot_fst : ((prod D E).bot).fst = D.bot := by rw [← pair_bot_bot, fst_pair]

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

@[simp] theorem prod_bot_snd : ((prod D E).bot).snd = E.bot := by rw [← pair_bot_bot, snd_pair]

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

/-- The inner application `fade(check(y), z)` of Scott's `smash(x, y) = fade(check(x),
fade(check(y), ⟨x, y⟩))`: here `z = ⟨x, y⟩` is passed through `idMap` (Scott's `⟨x,y⟩` *is* the
ambient input). -/
def smashFadeInner : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

/-- **Example 8.4(b)(ii)'s `smash` combinator.** `smash(x, y) = fade(check(x), fade(check(y),
⟨x, y⟩))`. -/
def smashRetraction : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) (smashFadeInner (D := D) (E := E)))

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- `g(f, y) = fade(check(y), f(y))`, as a joint approximable map `(D → E) × D → E`. -/
def strictEvalFade : ApproximableMap (prod (funSpace D E) D) E :=
  (fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- **Example 8.4(b)(i)'s `strict` combinator.** `strict(f) = λy. fade(check(y), f(y))`, built via
Theorem 3.12's `curry`. -/
def strictRetraction : ApproximableMap (funSpace D E) (funSpace D E) := curry strictEvalFade

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- The closed form of `strict`'s elementwise action: `strict(f)(y) = ⊥_E` if `y = ⊥_D`, else
`f(y)`. -/
theorem toApproxMap_strictRetraction_mem {φ : (funSpace D E).Element} {y : D.Element}
    {Z : Set β} :
    ((toApproxMap (strictRetraction.toElementMap φ)).toElementMap y).mem Z ↔
      E.mem Z ∧ (Z = E.master ∨ (y ≠ D.bot ∧ ((toApproxMap φ).toElementMap y).mem Z)) := by
  show ((toApproxMap ((curry strictEvalFade).toElementMap φ)).toElementMap y).mem Z ↔ _
  rw [toElementMap_curry_apply]
  show (((fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))).toElementMap
      (pair φ y)).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁, snd_pair,
    evalMap_apply, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

theorem strictRetraction_apply_bot (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap D.bot = E.bot := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hne, -⟩⟩
    · rfl
    · exact absurd rfl hne
  · rintro rfl
    exact ⟨E.master_mem, Or.inl rfl⟩

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- **`f` is a fixed point of `strict` iff `f` is strict.** -/
theorem isStrict_toApproxMap_of_fixed {φ : (funSpace D E).Element}
    (hφ : strictRetraction.toElementMap φ = φ) : Exercise510.IsStrict (toApproxMap φ) := by
  rw [Exercise510.isStrict_iff_apply_bot]
  have h := strictRetraction_apply_bot φ
  rwa [hφ] at h

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

theorem strictRetraction_apply_of_ne_bot {y : D.Element} (hy : y ≠ D.bot)
    (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap y
      = (toApproxMap φ).toElementMap y := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem]
  constructor
  · rintro ⟨-, rfl | ⟨-, hZ⟩⟩
    · exact ((toApproxMap φ).toElementMap y).master_mem
    · exact hZ
  · intro hZ
    exact ⟨((toApproxMap φ).toElementMap y).sub hZ, Or.inr ⟨hy, hZ⟩⟩

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

theorem toApproxMap_toFilter (f : ApproximableMap D E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv D E).right_inv f

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- Two tiny reproofs of `funSpaceEquiv`'s own round-trips, stated standalone so the closed-form
calculations below don't have to fight `OrderIso` field-access notation. -/
theorem toFilter_toApproxMap (φ : (funSpace D E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv D E).left_inv φ

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

theorem strictRetraction_fixed_of_isStrict {f : ApproximableMap D E} (hf : Exercise510.IsStrict f) :
    strictRetraction.toElementMap (toFilter f) = toFilter f := by
  have hbot : f.toElementMap D.bot = E.bot := Exercise510.isStrict_iff_apply_bot.mp hf
  have key : toApproxMap (strictRetraction.toElementMap (toFilter f)) = f := by
    apply ext_of_toElementMap
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot, hbot]
    · rw [strictRetraction_apply_of_ne_bot hy, toApproxMap_toFilter]
  rw [← toFilter_toApproxMap (strictRetraction.toElementMap (toFilter f)), key]

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- **Example 8.4(b)(i), the fixed-point representation.** Restricting `funSpaceEquiv` along
`isStrict_toApproxMap_of_fixed`/`strictRetraction_fixed_of_isStrict` identifies `Fix(strict)` with
the strict approximable maps `Exercise510.StrictMap D E`. -/
def strictRetractionFixIso :
    {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ} ≃o
      Exercise510.StrictMap D E where
  toFun φ := ⟨toApproxMap φ.1, isStrict_toApproxMap_of_fixed φ.2⟩
  invFun f := ⟨toFilter f.1, strictRetraction_fixed_of_isStrict f.2⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ φ'
    show toApproxMap φ.1 ≤ toApproxMap φ'.1 ↔ φ.1 ≤ φ'.1
    exact (funSpaceEquiv D E).map_rel_iff

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


/-- **The compactness lemma.** If neither coordinate of `z` is `⊥`, some *proper* smash
neighbourhood witnesses `z.mem Y ⊆ Z` for any `Z ∈ z` — built from `exists_mem_ne_master_of_ne_bot`
witnesses on each coordinate, intersected against `Z`'s own decomposition via the *filter*
`inter_mem` of `z.fst`/`z.snd` (no `NeighborhoodSystem`-level consistency witness needed). -/
theorem exists_smash_witness {z : (prod D E).Element} (hx : z.fst ≠ D.bot) (hy : z.snd ≠ E.bot)
    {Z : Set (α ⊕ β)} (hzZ : z.mem Z) :
    ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  obtain ⟨X0, hX0, hX0ne⟩ := exists_mem_ne_master_of_ne_bot hx
  obtain ⟨Y0, hY0, hY0ne⟩ := exists_mem_ne_master_of_ne_bot hy
  set A := Sum.inl ⁻¹' Z with hA
  set B := Sum.inr ⁻¹' Z with hB
  have hZeq : Z = prodNbhd A B := prodNbhd_preimage (z.sub hzZ)
  have hAmem : D.mem A := prod_mem_inl (z.sub hzZ)
  have hBmem : E.mem B := prod_mem_inr (z.sub hzZ)
  rw [hZeq] at hzZ
  have hzfA : z.fst.mem A := mem_fst.mpr ⟨hAmem, ((prod_mem_split hAmem hBmem).mp hzZ).1⟩
  have hzsB : z.snd.mem B := mem_snd.mpr ⟨hBmem, ((prod_mem_split hAmem hBmem).mp hzZ).2⟩
  have hzfX0' : z.fst.mem (X0 ∩ A) := z.fst.inter_mem hX0 hzfA
  have hzsY0' : z.snd.mem (Y0 ∩ B) := z.snd.inter_mem hY0 hzsB
  have hX0'mem : D.mem (X0 ∩ A) := z.fst.sub hzfX0'
  have hY0'mem : E.mem (Y0 ∩ B) := z.snd.sub hzsY0'
  have hX0'ne : X0 ∩ A ≠ D.master := Exercise510.inter_ne_master_left (z.fst.sub hX0) hX0ne
  have hY0'ne : Y0 ∩ B ≠ E.master := Exercise510.inter_ne_master_right (z.snd.sub hY0) hY0ne
  refine ⟨prodNbhd (X0 ∩ A) (Y0 ∩ B),
    Exercise510.smash_mem_proper hX0'mem hX0'ne hY0'mem hY0'ne, ?_, ?_⟩
  · exact (prod_mem_split hX0'mem hY0'mem).mpr
      ⟨(mem_fst.mp hzfX0').2, (mem_snd.mp hzsY0').2⟩
  · rw [hZeq]
    exact prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


theorem smashFadeInner_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashFadeInner.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧ (Z = (prod D E).master ∨ (z.snd ≠ E.bot ∧ z.mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁,
    toElementMap_idMap, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


theorem smashRetraction_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ (smashFadeInner.toElementMap z).mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) smashFadeInner)).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


/-- **`smashRetraction`'s closed form.** `smash(z) = z` if neither coordinate is `⊥`; otherwise
`smash(z) = ⊥`. -/
theorem smashRetraction_mem_iff {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ z.snd ≠ E.bot ∧ z.mem Z)) := by
  rw [smashRetraction_mem, smashFadeInner_mem]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨hx, hPZ', hZeq' | ⟨hy, hzZ⟩⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inl hZeq'⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hy, hzZ⟩⟩
  · rintro ⟨hPZ, hZeq | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hPZ, Or.inr ⟨hy, hzZ⟩⟩⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


theorem smashRetraction_le_idMap : smashRetraction (D := D) (E := E) ≤ idMap (prod D E) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_idMap]
  intro Z hZ
  rw [smashRetraction_mem_iff] at hZ
  rcases hZ with ⟨hPZ, rfl | ⟨-, -, hzZ⟩⟩
  · exact z.master_mem
  · exact hzZ

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


theorem smashRetraction_of_eq_bot {z : (prod D E).Element} (hz : z.fst = D.bot ∨ z.snd = E.bot) :
    smashRetraction.toElementMap z = (prod D E).bot := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hx, hy, -⟩⟩
    · rfl
    · exact absurd hz (by simp [hx, hy])
  · rintro rfl
    exact ⟨(prod D E).master_mem, Or.inl rfl⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


theorem smashRetraction_of_ne_bot {z : (prod D E).Element} (hx : z.fst ≠ D.bot)
    (hy : z.snd ≠ E.bot) : smashRetraction.toElementMap z = z := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨-, -, hzZ⟩⟩
    · rw [hZeq]; exact z.master_mem
    · exact hzZ
  · intro hzZ
    exact ⟨z.sub hzZ, Or.inr ⟨hx, hy, hzZ⟩⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


theorem isRetraction_smashRetraction : Retraction (smashRetraction (D := D) (E := E)) := by
  constructor
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_comp]
  by_cases hx : z.fst = D.bot
  · rw [smashRetraction_of_eq_bot (Or.inl hx),
      smashRetraction_of_eq_bot (Or.inl prod_bot_fst)]
  · by_cases hy : z.snd = E.bot
    · rw [smashRetraction_of_eq_bot (Or.inr hy),
        smashRetraction_of_eq_bot (Or.inr prod_bot_snd)]
    · rw [smashRetraction_of_ne_bot hx hy, smashRetraction_of_ne_bot hx hy]

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


/-- **The subsystem relation `Exercise510.smash D E ◁ prod D E`.** Every smash neighbourhood is a
product neighbourhood; a proper smash neighbourhood stays proper (hence smash-membership, not just
product-membership) after any consistent intersection, by `Exercise510.inter_ne_master_left/right`
exactly as in `Exercise510.smash`'s own closure proof. -/
theorem smash_subsystem_prod : Exercise510.smash D E ◁ prod D E where
  master_eq := by rw [Exercise510.smash_master, prod_master]
  sub := by
    rintro W (rfl | ⟨X, Y, hX, -, hY, -, rfl⟩)
    · exact prod_mem_prodNbhd D.master_mem E.master_mem
    · exact prod_mem_prodNbhd hX hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hPint
    · -- `W = smash master = prod master`.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (D.sub_master hX'),
          Set.inter_eq_right.mpr (E.sub_master hY')]
    · -- `W = prodNbhd X Y` proper.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (D.sub_master hX),
          Set.inter_eq_left.mpr (E.sub_master hY)]
      · -- both proper: `hPint` supplies the membership of the intersection in `prod D E`.
        rw [prodNbhd_inter] at hPint ⊢
        obtain ⟨hXX'mem, hYY'mem⟩ := prod_mem_prodNbhd_iff.mp hPint
        exact Or.inr ⟨X ∩ X', Y ∩ Y', hXX'mem, Exercise510.inter_ne_master_left hX hXne, hYY'mem,
          Exercise510.inter_ne_master_right hY hYne, rfl⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


/-- The closed form of `Subsystem.retractionOfSubsystem`'s elementwise action, specialized to
`smash_subsystem_prod`, simplified using that `z` is already up-closed: the existential witness
`X ⊆ Y ⊆ Z` of Proposition 8.2's formula collapses to `z.mem Y` directly. -/
theorem mem_toElementMap_retractionOfSubsystem_smash {z : (prod D E).Element}
    {Z : Set (α ⊕ β)} :
    ((Subsystem.retractionOfSubsystem (smash_subsystem_prod (D := D) (E := E))).toElementMap z).mem
        Z ↔
      (prod D E).mem Z ∧ ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hzX, hrel⟩
    obtain ⟨hPX, hPZ, Y, hSY, hXY, hYZ⟩ := (Subsystem.retractionOfSubsystem_rel _).mp hrel
    exact ⟨hPZ, Y, hSY, z.up_mem hzX (smash_subsystem_prod.sub hSY) hXY, hYZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    exact ⟨Y, hzY, (Subsystem.retractionOfSubsystem_rel _).mpr
      ⟨z.sub hzY, hPZ, Y, hSY, subset_rfl, hYZ⟩⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


/-- **Scott's `smash` combinator equals Proposition 8.2's canonical subsystem retraction.** Both
sides agree with `smashRetraction_mem_iff`'s closed form: the `Z = master` branch matches (both
sides always admit the master witness `Y = (smash D E).master`), and the "genuine pair" branch
matches by `exists_smash_witness` (`←`) and a direct case split on `(smash D E).mem Y` (`→`, using
that `Y ⊆ (prod D E).master` sandwiches `Z = master` when `Y` is itself the master, and that
`z.fst.mem`/`z.snd.mem` of a proper `Y`'s factors forces both coordinates non-`⊥`, `mem_bot`). -/
theorem smashRetraction_eq_retractionOfSubsystem :
    smashRetraction (D := D) (E := E) = Subsystem.retractionOfSubsystem smash_subsystem_prod := by
  apply ext_of_toElementMap
  intro z
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_toElementMap_retractionOfSubsystem_smash]
  constructor
  · rintro ⟨hPZ, rfl | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, (prod D E).master, Exercise510.smash_mem_iff.mpr (Or.inl rfl), z.master_mem,
        subset_rfl⟩
    · exact ⟨hPZ, exists_smash_witness hx hy hzZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    rcases Exercise510.smash_mem_iff.mp hSY with rfl | ⟨YA, YB, hYA, hYAne, hYB, hYBne, rfl⟩
    · exact ⟨hPZ, Or.inl (Set.Subset.antisymm ((prod D E).sub_master hPZ) hYZ)⟩
    · have hzfYA : z.fst.mem YA := mem_fst.mpr ⟨hYA, ((prod_mem_split hYA hYB).mp hzY).1⟩
      have hzsYB : z.snd.mem YB := mem_snd.mpr ⟨hYB, ((prod_mem_split hYA hYB).mp hzY).2⟩
      refine ⟨hPZ, Or.inr ⟨?_, ?_, z.up_mem hzY hPZ hYZ⟩⟩
      · intro hxbot; rw [hxbot, mem_bot] at hzfYA; exact hYAne hzfYA
      · intro hybot; rw [hybot, mem_bot] at hzsYB; exact hYBne hzsYB

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash


/-- **Example 8.4(b)(ii) (Scott 1981, PRG-19).** `smashRetraction` is a projection on `D × E`
whose fixed-point set is isomorphic to the smash product `Exercise510.smash D E`. -/
theorem example84b_smash :
    IsProjection (smashRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.smash D E).Element ≃o
        {z : (prod D E).Element // smashRetraction.toElementMap z = z}) := by
  rw [smashRetraction_eq_retractionOfSubsystem]
  exact ⟨Subsystem.isProjection_retractionOfSubsystem smash_subsystem_prod,
    ⟨Subsystem.elementIso smash_subsystem_prod⟩⟩

end Smash
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict


theorem strictRetraction_le_idMap : strictRetraction (D := D) (E := E) ≤ idMap (funSpace D E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap]
  have hmap : toApproxMap (strictRetraction.toElementMap φ) ≤ toApproxMap φ := by
    rw [le_iff_toElementMap_le]
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot]
      intro Z hZ
      rw [mem_bot] at hZ
      rw [hZ]
      exact ((toApproxMap φ).toElementMap D.bot).master_mem
    · rw [strictRetraction_apply_of_ne_bot hy]
  exact (funSpaceEquiv D E).map_rel_iff.mp hmap

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict


theorem toApproxMap_injective {a b : (funSpace D E).Element} (h : toApproxMap a = toApproxMap b) :
    a = b := by
  rw [← toFilter_toApproxMap a, ← toFilter_toApproxMap b, h]

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict


theorem isRetraction_strictRetraction : Retraction (strictRetraction (D := D) (E := E)) := by
  constructor
  apply ext_of_toElementMap
  intro φ
  rw [toElementMap_comp]
  apply toApproxMap_injective
  apply ext_of_toElementMap
  intro y
  by_cases hy : y = D.bot
  · rw [hy, strictRetraction_apply_bot, strictRetraction_apply_bot]
  · rw [strictRetraction_apply_of_ne_bot hy, strictRetraction_apply_of_ne_bot hy]

end Strict
end

section
open NeighborhoodSystem ApproximableMap ApproximableMap₂
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict


/-- **Example 8.4(b)(i) (Scott 1981, PRG-19).** `strictRetraction` is a projection on `D → E`
whose fixed-point set is isomorphic to the strict function space `Exercise510.strictFun D E`. -/
theorem example84b_strict :
    IsProjection (strictRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.strictFun D E).Element ≃o
        {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ}) :=
  ⟨⟨isRetraction_strictRetraction, strictRetraction_le_idMap⟩,
    ⟨strictRetractionFixIso.trans (Exercise510.strictFunEquiv D E).symm |>.symm⟩⟩

end Strict
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- The fixed-point set of `a`, as a bare type — matching `IsFinitary`'s witness type. -/
abbrev FixSet (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The candidate subdomain of Theorem 8.5's proof, `D = {X ∈ E ∣ X a X}`.** Built for *any*
approximable map `a : E → E` — the neighbourhood-system axioms need only `mono`/`inter_right` of
`a`, no projection or finitary hypothesis. (This is also exactly Theorem 8.6's `Fix(sub)` predicate
`X sub(f) X`, restated for a single map `a` in place of the function-space token `f`.) -/
def fixedNbhd (a : ApproximableMap E E) : NeighborhoodSystem α where
  mem X := E.mem X ∧ a.rel X X
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨E.master_mem, a.master_rel⟩
  inter_mem := by
    rintro X Y Z ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ ⟨hZE, _⟩ hZsub
    have hXYE : E.mem (X ∩ Y) := E.inter_mem hXE hYE hZE hZsub
    have h1 : a.rel (X ∩ Y) X :=
      a.mono hXa Set.inter_subset_left subset_rfl hXYE hXE
    have h2 : a.rel (X ∩ Y) Y :=
      a.mono hYa Set.inter_subset_right subset_rfl hXYE hYE
    exact ⟨hXYE, a.inter_right h1 h2⟩
  sub_master := fun h => E.sub_master h.1
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

@[simp] theorem fixedNbhd_mem {a : ApproximableMap E E} {X : Set α} :
    (fixedNbhd a).mem X ↔ E.mem X ∧ a.rel X X := Iff.rfl
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

instance instNonemptyMemSubtype (x : V.Element) : Nonempty {X : Set γ // x.mem X} :=
  ⟨⟨V.master, x.master_mem⟩⟩

end Algebraic
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

/-- **Compactness, as a standalone predicate**: `x` is compact iff every time `x` sits below a
directed union it already sits below one of the summands. By algebraicity, this is exactly the
same thing as being principal (`eq_principal_of_isCompactElt`). Stated with `I` fixed to `V`'s own
token universe (the only instantiation ever needed below), to sidestep spurious universe-metavariable
friction from a separately-auto-bound `Type*` inside a reusable `def`. -/
def IsCompactElt (x : V.Element) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k),
    x ≤ iSupDirected d hdir → ∃ i, x ≤ d i

end Algebraic
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section HardDirection

variable {a : ApproximableMap E E}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

/-- **The section `i : F → E`** induced by the abstract witness `e` of `IsFinitary a`: on the
principal element `↑X` of `F`, `i` returns the underlying `E`-element of `e.symm(↑X) ∈ Fix(a)`.
Built via `ofMono` (Exercise 2.8) — monotone on principals is all that's needed. -/
def sectionMap : ApproximableMap F E :=
  ofMono (fun _X hX => (e.symm (F.principal hX)).1) (fun _ _ hX hX' hXX' =>
    e.symm.monotone ((F.principal_le_iff hX hX').mpr hXX'))

end HardDirection
end

section
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
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section HardDirection

variable {a : ApproximableMap E E}


variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)


/-- **`e` distributes over directed sups of `a`-fixed families.** `Fix(a)` is not itself a
`NeighborhoodSystem.Element` type, so this is proved directly by antisymmetry (rather than via a
generic "order isos preserve directed sups" lemma): both inequalities reduce to `le_iSupDirected`/
`iSupDirected_le` on the `E`- and `F`-sides plus monotonicity of `e`/`e.symm`. -/
theorem e_apply_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i)
    (hSfix : a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir)
    (hdir' : ∀ i j : I, ∃ k, e ⟨d i, hfix i⟩ ≤ e ⟨d k, hfix k⟩ ∧
      e ⟨d j, hfix j⟩ ≤ e ⟨d k, hfix k⟩) :
    e ⟨iSupDirected d hdir, hSfix⟩ = iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' := by
  apply le_antisymm
  · have hstep : (⟨iSupDirected d hdir, hSfix⟩ : FixSet a) ≤
        e.symm (iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir') := by
      show iSupDirected d hdir ≤ _
      apply iSupDirected_le
      intro i
      show d i ≤ _
      have hle : e ⟨d i, hfix i⟩ ≤ iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' :=
        le_iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' i
      have := e.symm.monotone hle
      rwa [e.symm_apply_apply] at this
    have := e.monotone hstep
    rwa [e.apply_symm_apply] at this
  · apply iSupDirected_le
    intro i
    exact e.monotone (le_iSupDirected d hdir i)

end HardDirection
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}


/-- **Compact elements are principal** — the converse of `principal_isCompactElt`, via
algebraicity: test compactness against `x`'s own principal-approximant family. -/
theorem eq_principal_of_isCompactElt {x : V.Element} (hx : IsCompactElt x) :
    ∃ (X : Set γ) (hX : V.mem X), x = V.principal hX := by
  have hle : x ≤ iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := le_of_eq (eq_iSupDirected_principal x)
  obtain ⟨i0, hi0⟩ :=
    hx (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2)) (principalFamily_directed x) hle
  exact ⟨i0.1, x.sub i0.2, le_antisymm hi0 (principal_le_of_mem i0.2)⟩

end Algebraic
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **`fixedNbhd a ◁ E`, unconditionally.** The consistency clause is the same monotonicity +
intersectivity calculation as `fixedNbhd`'s own `inter_mem`, just without needing the extra
consistency witness `Z`. -/
theorem fixedNbhd_subsystem (a : ApproximableMap E E) : fixedNbhd a ◁ E where
  master_eq := rfl
  sub := fun h => h.1
  inter_closed := by
    rintro X Y ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ hEXY
    have h1 : a.rel (X ∩ Y) X := a.mono hXa Set.inter_subset_left subset_rfl hEXY hXE
    have h2 : a.rel (X ∩ Y) Y := a.mono hYa Set.inter_subset_right subset_rfl hEXY hYE
    exact ⟨hEXY, a.inter_right h1 h2⟩
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The "easy" (`⟸`) half of formula (ii), isolated.** Valid for **any** approximable map
`a : E → E` with **no hypothesis on `a` at all** — not even that `a` satisfies the rest of formula
(ii), let alone that it is a finitary projection. Pure monotonicity + up-closure: `↑X ≤ x`
(`principal_le_of_mem`) pushes `a`'s self-relation at `X` up to `x` (`toElementMap_mono`), and
`X ⊆ Y` finishes by up-closure. Isolated from `isFinitaryProjection_of_formula`'s own proof (where
it was the `←` branch of the `constructor`) because Exercise 8.27(b)(3) needs exactly this half,
unconditionally, for `a := piD d` — independently of whether the *rest* of formula (ii) holds. -/
theorem mem_of_exists_rel_self {a : ApproximableMap E E} (x : E.Element) {Y : Set α}
    (hYE : E.mem Y) {X : Set α} (hXx : x.mem X) (hXY : X ⊆ Y) (hXaX : a.rel X X) :
    (a.toElementMap x).mem Y := by
  have hX : E.mem X := a.rel_dom hXaX
  have hmem : (a.toElementMap (E.principal hX)).mem X := (a.rel_iff_mem_principal hX).mp hXaX
  have hle : E.principal hX ≤ x := principal_le_of_mem hXx
  have hXmem : (a.toElementMap x).mem X := (a.toElementMap_mono hle) X hmem
  exact (a.toElementMap x).up_mem hXmem hYE hXY
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Theorem 8.5, `(ii) ⟹ (i)` (Scott 1981, PRG-19).** If `a` satisfies Scott's step-closure
formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`, then `a` is a finitary projection.

The proof shows `a` literally *is* `retractionOfSubsystem` for `D = fixedNbhd a`: unwinding formula
(ii) at a principal `x = ↑X` via `rel_iff_mem_principal` reproduces exactly
`retractionOfSubsystem_rel`'s formula. Definition 8.3's corollaries of Proposition 8.2 then finish
the proof — no further work needed. -/
theorem isFinitaryProjection_of_formula (a : ApproximableMap E E)
    (hii : ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) :
    FinitaryProjection a := by
  have heq : a = Subsystem.retractionOfSubsystem (fixedNbhd_subsystem a) := by
    apply ApproximableMap.ext
    intro X Z
    rw [Subsystem.retractionOfSubsystem_rel]
    constructor
    · intro hr
      have hX : E.mem X := a.rel_dom hr
      have hmem : (a.toElementMap (E.principal hX)).mem Z := (a.rel_iff_mem_principal hX).mp hr
      obtain ⟨hZE, Y, hXY, hYZ, hYa⟩ := hii (E.principal hX) |>.mp hmem
      exact ⟨hX, hZE, Y, ⟨a.rel_dom hYa, hYa⟩, (E.mem_principal hX).mp hXY |>.2, hYZ⟩
    · rintro ⟨hX, hZ, Y, ⟨_, hYa⟩, hXY, hYZ⟩
      exact (a.rel_iff_mem_principal hX).mpr
        (mem_of_exists_rel_self (E.principal hX) hZ (E.mem_principal hX |>.mpr ⟨a.rel_dom hYa, hXY⟩)
          hYZ hYa)
  rw [heq]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem a)
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}


/-- **Principal elements are compact**: if `↑X ⊑ ⋃ᵢ dᵢ` for a directed family, then already
`↑X ⊑ dᵢ` for some single `i`. Immediate from `X ∈ ↑X` and `mem_iSupDirected`. -/
theorem principal_compact {X : Set γ} (hX : V.mem X) {I : Type*} [Nonempty I]
    (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
    (h : V.principal hX ≤ iSupDirected d hdir) : ∃ i, V.principal hX ≤ d i := by
  obtain ⟨i, hi⟩ := (mem_iSupDirected d hdir).mp (h X ⟨hX, subset_rfl⟩)
  exact ⟨i, fun _ ⟨hW, hXW⟩ => (d i).up_mem hi hW hXW⟩

end Algebraic
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}


theorem principal_isCompactElt {X : Set γ} (hX : V.mem X) : IsCompactElt (V.principal hX) :=
  fun d hdir h => principal_compact hX d hdir h

end Algebraic
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section HardDirection

variable {a : ApproximableMap E E}

/-- Idempotency of a retraction at the element level: `a(a(z)) = a(z)`. -/
theorem toElementMap_idem {a : ApproximableMap E E} (ha : Retraction a) (z : E.Element) :
    a.toElementMap (a.toElementMap z) = a.toElementMap z := by
  rw [← toElementMap_comp a a z, ha.out]

end HardDirection
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

section HardDirection

variable {a : ApproximableMap E E}


variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)


/-- **Scott's compactness-reflection fact.** If `e.symm(w')` is a *principal* (finite) element of
`F`, then `e.symm(w')`'s image `.1` in `E` need not be principal; the content here is the converse
direction: **pulling a genuinely principal element of `F` back through `e.symm` always lands on a
principal element of `E`.** The key step lifts compactness across the retraction: any `E`-directed
family bounding `(e.symm(↑Y)).1` from above can be replaced (applying the continuous, idempotent
`a`) by an `a`-fixed directed family with the same sup-relationship, and `a ≤ idMap E` (`a` is a
*projection*, not just a retraction) is exactly what lets the bound transfer back down. -/
theorem exists_principal_eq_of_isRetraction_le_idMap (ha_ret : Retraction a)
    (ha_proj : a ≤ idMap E) {Y : Set β} (hY : F.mem Y) :
    ∃ (X : Set α) (hX : E.mem X), (e.symm (F.principal hY)).1 = E.principal hX := by
  apply eq_principal_of_isCompactElt
  intro I _ d hdir hle
  set d2 : I → E.Element := fun i => a.toElementMap (d i) with hd2
  have hdir2 : ∀ i j, ∃ k, d2 i ≤ d2 k ∧ d2 j ≤ d2 k := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, a.toElementMap_mono hik, a.toElementMap_mono hjk⟩
  have hfix2 : ∀ i, a.toElementMap (d2 i) = d2 i := fun i => toElementMap_idem ha_ret (d i)
  have hle2 : (e.symm (F.principal hY)).1 ≤ iSupDirected d2 hdir2 := by
    calc (e.symm (F.principal hY)).1 = a.toElementMap (e.symm (F.principal hY)).1 :=
          (e.symm (F.principal hY)).2.symm
      _ ≤ a.toElementMap (iSupDirected d hdir) := a.toElementMap_mono hle
      _ = iSupDirected d2 hdir2 := toElementMap_iSupDirected a d hdir
  have hSfix2 : a.toElementMap (iSupDirected d2 hdir2) = iSupDirected d2 hdir2 :=
    toElementMap_iSupDirected_fixed d2 hdir2 hfix2
  have hdir2' : ∀ i j : I, ∃ k, e ⟨d2 i, hfix2 i⟩ ≤ e ⟨d2 k, hfix2 k⟩ ∧
      e ⟨d2 j, hfix2 j⟩ ≤ e ⟨d2 k, hfix2 k⟩ := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir2 i j
    exact ⟨k, e.monotone hik, e.monotone hjk⟩
  have hle3 : F.principal hY ≤ iSupDirected (fun i => e ⟨d2 i, hfix2 i⟩) hdir2' := by
    have h1 : e ⟨(e.symm (F.principal hY)).1, (e.symm (F.principal hY)).2⟩ ≤
        e ⟨iSupDirected d2 hdir2, hSfix2⟩ := e.monotone hle2
    rwa [Subtype.coe_eta, e.apply_symm_apply,
      e_apply_iSupDirected_fixed e d2 hdir2 hfix2 hSfix2 hdir2'] at h1
  obtain ⟨i0, hi0⟩ := principal_isCompactElt hY _ _ hle3
  have hi0' : e.symm (F.principal hY) ≤ ⟨d2 i0, hfix2 i0⟩ := by
    have := e.symm.monotone hi0
    rwa [e.symm_apply_apply] at this
  have hfinal : (e.symm (F.principal hY)).1 ≤ d2 i0 := hi0'
  have hd2le : d2 i0 ≤ d i0 := by
    have := (le_iff_toElementMap_le.mp ha_proj) (d i0)
    rwa [toElementMap_idMap] at this
  exact ⟨i0, hfinal.trans hd2le⟩

end HardDirection
end

section
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
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

end
end DomainTheory.NeighbourhoodSystems
end
