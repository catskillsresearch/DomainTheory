module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_17
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_12
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

/- concordance: source L5195 EXERCISE 8.22 comparing B and C -/
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- `C` is positive: every `C`-neighbourhood (a cone or a singleton) is nonempty. -/
theorem C_nonempty : ∀ X, C.mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- Doubles every bit of a string: `enc [] = []`, `enc (b :: σ) = b :: b :: enc σ`. -/
def enc : Str → Str
  | [] => []
  | b :: σ => b :: b :: enc σ

/-- The "completed" encoding: `enc σ` followed by the two-bit marker `[true, false]`, which can
never arise as a doubled block `[b, b]`. -/
def encC (σ : Str) : Str := enc σ ++ [true, false]

@[simp] theorem enc_nil : enc ([] : Str) = [] := rfl

@[simp] theorem enc_cons (b : Bool) (σ : Str) : enc (b :: σ) = b :: b :: enc σ := rfl

theorem encC_cons (b : Bool) (σ : Str) : encC (b :: σ) = b :: b :: encC σ := by
  simp [encC]

theorem encC_nil : encC ([] : Str) = [true, false] := rfl

theorem enc_append (σ τ : Str) : enc (σ ++ τ) = enc σ ++ enc τ := by
  induction σ with
  | nil => simp
  | cons b σ' ih => simp [ih]

theorem enc_length (σ : Str) : (enc σ).length = 2 * σ.length := by
  induction σ with
  | nil => simp
  | cons b σ' ih => simp [ih]; ring

theorem encC_length (σ : Str) : (encC σ).length = 2 * σ.length + 2 := by
  simp [encC, enc_length]

/-- **Two completions relate only to themselves.** `encC σ <+: encC τ ↔ σ = τ`: distinct completed
positions of `C` become disjoint (never nested) `B`-cones. -/
theorem encC_prefix_encC_iff {σ τ : Str} : encC σ <+: encC τ ↔ σ = τ := by
  constructor
  · induction σ generalizing τ with
    | nil =>
      intro h
      cases τ with
      | nil => rfl
      | cons c τ' =>
        exfalso
        rw [encC_nil, encC_cons] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
        exact absurd h3 (by decide)
    | cons b σ' ih =>
      intro h
      cases τ with
      | nil =>
        exfalso
        rw [encC_cons, encC_nil] at h
        have hlen := h.length_le
        simp only [List.length_cons, List.length_nil, encC_length] at hlen
        omega
      | cons c τ' =>
        rw [encC_cons, encC_cons] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨-, h3⟩ := List.cons_prefix_cons.mp h2
        rw [ih h3]
  · rintro rfl; exact List.prefix_rfl

theorem encC_injective {σ τ : Str} (h : encC σ = encC τ) : σ = τ :=
  encC_prefix_encC_iff.mp (h ▸ List.prefix_rfl)

theorem enc_prefix_of_prefix {σ τ : Str} (h : σ <+: τ) : enc σ <+: enc τ := by
  obtain ⟨t, rfl⟩ := h
  rw [enc_append]
  exact ⟨enc t, rfl⟩

/-- **The marker never collides with a real prefix.** `enc ρ <+: encC σ` exactly reproduces `C`'s
own "cone ⊆ completed" relation `ρ <+: σ`: the extra length used by the marker can never be
matched by a genuine (doubled) continuation, since `[b, b] ≠ [true, false]`. -/
theorem enc_prefix_encC_iff {ρ σ : Str} : enc ρ <+: encC σ ↔ ρ <+: σ := by
  constructor
  · induction ρ generalizing σ with
    | nil => intro _; exact List.nil_prefix
    | cons b ρ' ih =>
      intro h
      cases σ with
      | nil =>
        exfalso
        rw [enc_cons, encC_nil] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
        exact absurd h3 (by decide)
      | cons c σ' =>
        rw [enc_cons, encC_cons] at h
        obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
        obtain ⟨-, h3⟩ := List.cons_prefix_cons.mp h2
        rw [List.cons_prefix_cons]
        exact ⟨rfl, ih h3⟩
  · intro h
    calc enc ρ <+: enc σ := enc_prefix_of_prefix h
      _ <+: encC σ := ⟨[true, false], rfl⟩

/-- **`enc` is prefix-reflecting.** Doubling never merges or confuses distinct prefixes: a prefix
relation between doubled strings comes from a prefix relation between the originals. -/
theorem enc_prefix_iff {σ τ : Str} : enc σ <+: enc τ ↔ σ <+: τ := by
  refine ⟨?_, enc_prefix_of_prefix⟩
  induction σ generalizing τ with
  | nil => intro _; exact List.nil_prefix
  | cons b σ' ih =>
    cases τ with
    | nil =>
      intro h
      rw [enc_cons, enc_nil] at h
      obtain ⟨t, ht⟩ := h
      simp at ht
    | cons c τ' =>
      intro h
      rw [enc_cons, enc_cons, List.cons_prefix_cons, List.cons_prefix_cons] at h
      obtain ⟨rfl, -, h3⟩ := h
      rw [List.cons_prefix_cons]
      exact ⟨rfl, ih h3⟩

theorem enc_injective {σ τ : Str} (h : enc σ = enc τ) : σ = τ := by
  have h1 : σ <+: τ := enc_prefix_iff.mp ⟨[], by simpa using h⟩
  have h2 : τ <+: σ := enc_prefix_iff.mp ⟨[], by simpa using h.symm⟩
  exact h1.eq_of_length (h1.length_le.antisymm h2.length_le)

/-- The image family: `B`-cones re-encoding `C`'s cones (`enc`) and completions (`encC`). -/
def memD' (X : Set Str) : Prop := (∃ σ, X = cone (enc σ)) ∨ (∃ σ, X = cone (encC σ))

/-- Every `D'`-set is literally a `B`-cone, so nestedness-or-disjointness is free from `B`'s own
`cone_trichotomy`. -/
theorem D'_nestedOrDisjoint : NestedOrDisjoint memD' := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact cone_trichotomy (enc σ) (enc τ)
  · exact cone_trichotomy (enc σ) (encC τ)
  · exact cone_trichotomy (encC σ) (enc τ)
  · exact cone_trichotomy (encC σ) (encC τ)

/-- **The image neighbourhood system `D'`.** -/
def D' : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memD' Set.univ ⟨[], Set.mem_univ _⟩
    (Or.inl ⟨[], by rw [enc_nil, cone_nil]⟩)
    D'_nestedOrDisjoint (by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact Set.subset_univ _)

@[simp] theorem D'_mem {X : Set Str} : D'.mem X ↔ memD' X := Iff.rfl

@[simp] theorem D'_master : D'.master = (Set.univ : Set Str) := rfl

/-- **`D' ◁ B`.** Same master; `D'.mem ⊆ B.mem` since every `D'`-set is a `B`-cone; and
consistency is inherited via `D'_nestedOrDisjoint` exactly as in `B_subsystem_C`. -/
theorem D'_subsystem_B : D' ◁ B where
  master_eq := rfl
  sub := by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact ⟨_, rfl⟩
  inter_closed := by
    rintro X Y hX hY hBXY
    rcases D'_nestedOrDisjoint hX hY with h | h | h
    · rw [Set.inter_eq_left.mpr h]; exact hX
    · rw [Set.inter_eq_right.mpr h]; exact hY
    · rw [h] at hBXY; exact absurd (B_nonempty ∅ hBXY) (by simp)

theorem cone_encC_subset_cone_enc_iff {σ τ : Str} : cone (encC σ) ⊆ cone (enc τ) ↔ τ <+: σ := by
  rw [cone_subset_cone, enc_prefix_encC_iff]

theorem cone_encC_subset_iff {σ τ : Str} : cone (encC σ) ⊆ cone (encC τ) ↔ σ = τ := by
  rw [cone_subset_cone, encC_prefix_encC_iff, eq_comm]

theorem cone_enc_subset_iff {σ τ : Str} : cone (enc σ) ⊆ cone (enc τ) ↔ τ <+: σ := by
  rw [cone_subset_cone, enc_prefix_iff]

theorem cone_ne_singleton (σ τ : Str) : cone σ ≠ ({τ} : Set Str) := by
  intro h
  have h1 : σ ∈ cone σ := List.prefix_rfl
  have h2 : σ ++ [true] ∈ cone σ := ⟨[true], rfl⟩
  rw [h] at h1 h2
  simp only [Set.mem_singleton_iff] at h1 h2
  exact absurd (h2.trans h1.symm) (by simp)

/-- **No `B`-cone reaches "past" a completion.** `encC σ` is never a prefix of `enc τ`: a
"completed" position of `C` never contains, as a subset, a "still going" cone. -/
theorem not_encC_prefix_enc {σ τ : Str} : ¬ encC σ <+: enc τ := by
  induction σ generalizing τ with
  | nil =>
    cases τ with
    | nil => simp [encC_nil]
    | cons c τ' =>
      rw [encC_nil, enc_cons]
      intro h
      obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
      obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
      exact absurd h3 (by decide)
  | cons b σ' ih =>
    cases τ with
    | nil =>
      rw [encC_cons, enc_nil]
      intro h
      exact absurd h.length_le (by simp)
    | cons c τ' =>
      rw [encC_cons, enc_cons]
      intro h
      obtain ⟨rfl, h2⟩ := List.cons_prefix_cons.mp h
      obtain ⟨-, h3⟩ := List.cons_prefix_cons.mp h2
      exact ih h3

theorem enc_ne_encC (σ τ : Str) : enc σ ≠ encC τ := by
  intro h
  exact not_encC_prefix_enc (σ := τ) (τ := σ) (h ▸ List.prefix_rfl)

theorem not_cone_enc_subset_cone_encC {σ τ : Str} : ¬ cone (enc σ) ⊆ cone (encC τ) := by
  rw [cone_subset_cone]; exact not_encC_prefix_enc

/-- **Inverse half of `C ≅ᴰ D'`.** -/
def fromD' (y : D'.Element) : C.Element where
  mem X := (∃ σ, y.mem (cone (enc σ)) ∧ X = cone σ) ∨ (∃ σ, y.mem (cone (encC σ)) ∧ X = ({σ} : Set Str))
  sub := by
    rintro X (⟨σ, -, rfl⟩ | ⟨σ, -, rfl⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  master_mem := by
    refine Or.inl ⟨[], ?_, cone_nil.symm⟩
    rw [enc_nil, cone_nil, ← D'_master]
    exact y.master_mem
  inter_mem := by
    rintro X X' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩)
    · -- cone/cone
      have hy := y.inter_mem hσ hτ
      rcases cone_trichotomy (enc σ) (enc τ) with h | h | h
      · exact Or.inl ⟨σ, hσ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr
          (cone_enc_subset_iff.mp h))]⟩
      · exact Or.inl ⟨τ, hτ, by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr
          (cone_enc_subset_iff.mp h))]⟩
      · rw [h] at hy; exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
    · -- cone/completion
      have hy := y.inter_mem hσ hτ
      rcases cone_trichotomy (enc σ) (encC τ) with h | h | h
      · exfalso
        exact absurd h not_cone_enc_subset_cone_encC
      · exact Or.inr ⟨τ, hτ, by rw [Set.inter_eq_right.mpr (singleton_subset_cone.mpr
          (cone_encC_subset_cone_enc_iff.mp h))]⟩
      · rw [h] at hy; exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
    · -- completion/cone
      have hy := y.inter_mem hσ hτ
      rcases cone_trichotomy (encC σ) (enc τ) with h | h | h
      · exact Or.inr ⟨σ, hσ, by rw [Set.inter_eq_left.mpr (singleton_subset_cone.mpr
          (cone_encC_subset_cone_enc_iff.mp h))]⟩
      · exfalso
        exact absurd h not_cone_enc_subset_cone_encC
      · rw [h] at hy; exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
    · -- completion/completion
      have hy := y.inter_mem hσ hτ
      by_cases hστ : σ = τ
      · subst hστ
        exact Or.inr ⟨σ, hσ, by rw [Set.inter_self]⟩
      · exfalso
        have h' : cone (encC σ) ∩ cone (encC τ) = ∅ := by
          rcases cone_trichotomy (encC σ) (encC τ) with h | h | h
          · exact absurd (cone_encC_subset_iff.mp h) hστ
          · exact absurd (cone_encC_subset_iff.mp h) (Ne.symm hστ)
          · exact h
        rw [h'] at hy
        exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
  up_mem := by
    rintro X X' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) hX' hsub
    · rcases hX' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := cone_subset_cone.mp hsub
        exact y.up_mem hσ (Or.inl ⟨κ, rfl⟩) (cone_enc_subset_iff.mpr hκσ)
      · exfalso
        have h1 : σ ∈ cone σ := List.prefix_rfl
        have h2 : σ ++ [true] ∈ cone σ := ⟨[true], rfl⟩
        have hσκ1 : σ = κ := hsub h1
        have hσκ2 : σ ++ [true] = κ := hsub h2
        exact absurd (hσκ2.trans hσκ1.symm) (by simp)
    · rcases hX' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := singleton_subset_cone.mp hsub
        exact y.up_mem hσ (Or.inl ⟨κ, rfl⟩) (cone_encC_subset_cone_enc_iff.mpr hκσ)
      · refine Or.inr ⟨κ, ?_, rfl⟩
        have hσκ : σ = κ := hsub rfl
        exact y.up_mem hσ (Or.inr ⟨κ, rfl⟩) (cone_encC_subset_iff.mpr hσκ)

/-- **Forward half of `C ≅ᴰ D'`.** Sends a `C`-element `x` to the `D'`-element recording, for each
`D'`-shape, whether `x` reaches the corresponding `C`-neighbourhood. -/
def toD' (x : C.Element) : D'.Element where
  mem W := (∃ σ, x.mem (cone σ) ∧ W = cone (enc σ)) ∨ (∃ σ, x.mem ({σ} : Set Str) ∧ W = cone (encC σ))
  sub := by
    rintro W (⟨σ, -, rfl⟩ | ⟨σ, -, rfl⟩)
    · exact Or.inl ⟨σ, rfl⟩
    · exact Or.inr ⟨σ, rfl⟩
  master_mem := by
    rw [D'_master]
    refine Or.inl ⟨[], ?_, ?_⟩
    · rw [cone_nil]; exact x.master_mem
    · rw [enc_nil, cone_nil]
  inter_mem := by
    rintro W W' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩)
    · -- cone/cone
      have hx := x.inter_mem hσ hτ
      rcases cone_trichotomy σ τ with h | h | h
      · exact Or.inl ⟨σ, hσ, by rw [Set.inter_eq_left.mpr
          (cone_enc_subset_iff.mpr (cone_subset_cone.mp h))]⟩
      · exact Or.inl ⟨τ, hτ, by rw [Set.inter_eq_right.mpr
          (cone_enc_subset_iff.mpr (cone_subset_cone.mp h))]⟩
      · rw [h] at hx; exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
    · -- cone/singleton
      have hx := x.inter_mem hσ hτ
      rcases singleton_cone_nd σ τ with h | h | h
      · exact Or.inr ⟨τ, hτ, by rw [Set.inter_eq_right.mpr
          (cone_encC_subset_cone_enc_iff.mpr (singleton_subset_cone.mp h))]⟩
      · exfalso
        have h1 : σ ∈ cone σ := List.prefix_rfl
        have h2 : σ ++ [true] ∈ cone σ := ⟨[true], rfl⟩
        have hστ1 : σ = τ := h h1
        have hστ2 : σ ++ [true] = τ := h h2
        exact absurd (hστ2.trans hστ1.symm) (by simp)
      · exfalso
        have h' : cone σ ∩ {τ} = ∅ := by rw [Set.inter_comm]; exact h
        rw [h'] at hx
        exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
    · -- singleton/cone
      have hx := x.inter_mem hσ hτ
      rcases singleton_cone_nd τ σ with h | h | h
      · exact Or.inr ⟨σ, hσ, by rw [Set.inter_eq_left.mpr
          (cone_encC_subset_cone_enc_iff.mpr (singleton_subset_cone.mp h))]⟩
      · exfalso
        have h1 : τ ∈ cone τ := List.prefix_rfl
        have h2 : τ ++ [true] ∈ cone τ := ⟨[true], rfl⟩
        have hτσ1 : τ = σ := h h1
        have hτσ2 : τ ++ [true] = σ := h h2
        exact absurd (hτσ2.trans hτσ1.symm) (by simp)
      · exfalso
        rw [h] at hx
        exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
    · -- singleton/singleton
      have hx := x.inter_mem hσ hτ
      by_cases hστ : σ = τ
      · subst hστ
        exact Or.inr ⟨σ, hσ, by rw [Set.inter_self]⟩
      · exfalso
        have h' : ({σ} : Set Str) ∩ {τ} = ∅ := by
          ext w; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          rintro rfl; exact hστ
        rw [h'] at hx
        exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
  up_mem := by
    rintro W W' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) hW' hsub
    · rcases hW' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := cone_enc_subset_iff.mp hsub
        exact x.up_mem hσ (memC_cone κ) (cone_subset_cone.mpr hκσ)
      · exact absurd hsub not_cone_enc_subset_cone_encC
    · rcases hW' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := cone_encC_subset_cone_enc_iff.mp hsub
        exact x.up_mem hσ (memC_cone κ) (singleton_subset_cone.mpr hκσ)
      · refine Or.inr ⟨κ, ?_, rfl⟩
        have hστ : σ = κ := cone_encC_subset_iff.mp hsub
        exact hστ ▸ hσ

@[simp] theorem toD'_mem_enc {x : C.Element} (κ : Str) :
    (toD' x).mem (cone (enc κ)) ↔ x.mem (cone κ) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · have hκσ : κ = σ := enc_injective (cone_injective heq)
      rw [hκσ]; exact hσ
    · exact absurd (cone_injective heq) (enc_ne_encC κ σ)
  · intro hx; exact Or.inl ⟨κ, hx, rfl⟩

@[simp] theorem toD'_mem_encC {x : C.Element} (κ : Str) :
    (toD' x).mem (cone (encC κ)) ↔ x.mem ({κ} : Set Str) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · exact absurd (cone_injective heq).symm (enc_ne_encC σ κ)
    · have hκσ : κ = σ := encC_injective (cone_injective heq)
      rw [hκσ]; exact hσ
  · intro hx; exact Or.inr ⟨κ, hx, rfl⟩

@[simp] theorem fromD'_mem_cone {y : D'.Element} (κ : Str) :
    (fromD' y).mem (cone κ) ↔ y.mem (cone (enc κ)) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · have hκσ : κ = σ := cone_injective heq
      rw [hκσ]; exact hσ
    · exact absurd heq (cone_ne_singleton κ σ)
  · intro hy; exact Or.inl ⟨κ, hy, rfl⟩

@[simp] theorem fromD'_mem_singleton {y : D'.Element} (κ : Str) :
    (fromD' y).mem ({κ} : Set Str) ↔ y.mem (cone (encC κ)) := by
  constructor
  · rintro (⟨σ, hσ, heq⟩ | ⟨σ, hσ, heq⟩)
    · exact absurd heq.symm (cone_ne_singleton σ κ)
    · have hκσ : κ = σ := by
        have h1 : κ ∈ ({σ} : Set Str) := heq ▸ rfl
        simpa using h1
      rw [hκσ]; exact hσ
  · intro hy; exact Or.inr ⟨κ, hy, rfl⟩

theorem fromD'_toD' (x : C.Element) : fromD' (toD' x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · exact (toD'_mem_enc σ).mp hσ
    · exact (toD'_mem_encC σ).mp hσ
  · intro hX
    rcases x.sub hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
    · exact Or.inl ⟨σ, (toD'_mem_enc σ).mpr hX, rfl⟩
    · exact Or.inr ⟨σ, (toD'_mem_encC σ).mpr hX, rfl⟩

theorem toD'_fromD' (y : D'.Element) : toD' (fromD' y) = y := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (⟨κ, hκ, rfl⟩ | ⟨κ, hκ, rfl⟩)
    · exact (fromD'_mem_cone κ).mp hκ
    · exact (fromD'_mem_singleton κ).mp hκ
  · intro hW
    rcases y.sub hW with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
    · exact Or.inl ⟨κ, (fromD'_mem_cone κ).mpr hW, rfl⟩
    · exact Or.inr ⟨κ, (fromD'_mem_singleton κ).mpr hW, rfl⟩

/-- **`C ≅ᴰ D'`.** -/
def cdEquiv : C.Element ≃o D'.Element where
  toFun := toD'
  invFun := fromD'
  left_inv := fromD'_toD'
  right_inv := toD'_fromD'
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases x.sub hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
      · exact (toD'_mem_enc σ).mp (h _ ((toD'_mem_enc σ).mpr hX))
      · exact (toD'_mem_encC σ).mp (h _ ((toD'_mem_encC σ).mpr hX))
    · intro h W hW
      rcases hW with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact Or.inl ⟨σ, h _ hσ, rfl⟩
      · exact Or.inr ⟨σ, h _ hσ, rfl⟩

/-- **`B` is a literal subsystem of `C`** (Definition 6.10): every `B`-neighbourhood is already a
`C`-neighbourhood, and consistency is inherited — if two cones intersect to a `C`-neighbourhood
(hence nonempty), `cone_trichotomy` rules out the disjoint case, so the intersection is already the
smaller of the two cones. -/
theorem B_subsystem_C : B ◁ C where
  master_eq := rfl
  sub := by rintro X ⟨σ, rfl⟩; exact memC_cone σ
  inter_closed := by
    rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩ hCXY
    rcases cone_trichotomy σ τ with h | h | h
    · rw [Set.inter_eq_left.mpr h]; exact ⟨σ, rfl⟩
    · rw [Set.inter_eq_right.mpr h]; exact ⟨τ, rfl⟩
    · rw [h] at hCXY; exact absurd (C_nonempty ∅ hCXY) (by simp)

/-- **`B ⊴ C`** (Exercise 8.22). The projection Scott asks us to notice: the identity inclusion
`B ◁ C`. -/
theorem B_trianglelefteq_C : B ⊴ C :=
  Subsystem.trianglelefteq B_subsystem_C

theorem C_isomorphic_D' : C ≅ᴰ D' := ⟨cdEquiv⟩

/-- **`C ⊴ B`.** The nontrivial half of Exercise 8.22: `C` (finite-or-infinite binary sequences)
embeds as a subdomain of `B` (infinite binary sequences) via the bit-doubling re-encoding
`enc`/`encC` and the image subsystem `D' ◁ B`. -/
theorem C_trianglelefteq_B : C ⊴ B := ⟨D', D'_subsystem_B, C_isomorphic_D'⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
