module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26

@[expose] public section

@[expose] public section

/- concordance: source L5147 EXERCISE 8.12 integer presentation of U -/
-- Exercise812/affine_2.lean
namespace DomainTheory.NeighbourhoodSystems
namespace affine

open NeighborhoodSystem

end affine
end DomainTheory.NeighbourhoodSystems

/-! ### Exercise 8.12(c)–(e) (moved from Exercise_8_15 monolith) -/

namespace DomainTheory.NeighbourhoodSystems

namespace inter
open NeighborhoodSystem

/-- **`A ∩ (M \ Z) = A \ Z` whenever `A ⊆ M`**: needed to turn a `genAtom`-style "intersect with
`M \ Z`" step into a literal `A \ Z` once `A` is known to already lie inside `M`. Generic set-theory
fact, used by 8.12(c)(vi)(5)(b)'s `genAtom.combinedX_succ_eq` below. -/
theorem diff_eq_diff_of_subset {γ : Type*} {A M Z : Set γ} (h : A ⊆ M) :
    A ∩ (M \ Z) = A \ Z := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hxA, -, hxZ⟩; exact ⟨hxA, hxZ⟩
  · rintro ⟨hxA, hxZ⟩; exact ⟨hxA, h hxA, hxZ⟩

theorem mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    {A B : Set γ} (hA : A = ∅ ∨ D.mem A) (hB : D.mem B) : A ∩ B = ∅ ∨ D.mem (A ∩ B) := by
  rcases hA with rfl | hA
  · exact Or.inl (Set.empty_inter B)
  · rcases Set.eq_empty_or_nonempty (A ∩ B) with h | h
    · exact Or.inl h
    · exact Or.inr ((hpos hA hB).mpr h)

end inter
open NeighborhoodSystem

/-- **Generalization of `Theorem88.lean`'s `SplitSpec`.** -/
def SplitSpec' {α γ : Type*} (E : NeighborhoodSystem γ)
    (split : Set α → Set γ → Set α → Set γ × Set γ) : Prop :=
  ∀ {A : Set α} {B : Set γ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ E.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ E.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ E.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- The shared sign-interleaving map: at even positions, the `X`-sub-step's own bit; at odd
positions, the `Y`-sub-step's own bit. -/
def combinedδ (δ : ℕ → Bool × Bool) (n : ℕ) : Bool :=
  if n % 2 = 0 then (δ (n / 2)).1 else (δ (n / 2)).2

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne in
theorem combinedδ_even (δ : ℕ → Bool × Bool) (k : ℕ) : combinedδ δ (2 * k) = (δ k).1 := by
  unfold combinedδ
  rw [ite_eq_left (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne in
theorem combinedδ_odd (δ : ℕ → Bool × Bool) (k : ℕ) : combinedδ δ (2 * k + 1) = (δ k).2 := by
  unfold combinedδ
  rw [ite_eq_right (by omega : ¬ (2 * k + 1) % 2 = 0), show (2 * k + 1) / 2 = k from by omega]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- The de-interleaving map: reads `δ'`'s values two at a time, `(δ' (2*k), δ' (2*k+1))`, as the
`k`-th pair of bits — the inverse of `combinedδ`. -/
def deinterleaveδ (δ' : ℕ → Bool) (k : ℕ) : Bool × Bool := (δ' (2 * k), δ' (2 * k + 1))

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne in
/-- **Round-trip identity** (Exercise 8.12(c)(vi)(5)(c)(1)): re-interleaving `deinterleaveδ δ'`
recovers `δ'` exactly. Proved by `funext` plus a parity case split on the point `m`, closed by
`combinedδ_even`/`combinedδ_odd` and `omega`. -/
theorem combinedδ_deinterleaveδ (δ' : ℕ → Bool) :
    combinedδ (deinterleaveδ δ') = δ' := by
  funext m
  unfold combinedδ deinterleaveδ
  split
  · rename_i hm
    rw [show 2 * (m / 2) = m from by omega]
  · rename_i hm
    rw [show 2 * (m / 2) + 1 = m from by omega]

end AtomPair
end

/-- **Generalization of `Theorem88.lean`'s `exists_split`** to an abstract atomless `E`. -/
theorem exists_split' {α γ : Type*} {E : NeighborhoodSystem γ} (hEnomin : E.NoMinimal)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    ∃ I J : Set γ, (I = ∅ ∨ E.mem I) ∧ (J = ∅ ∨ E.mem J) ∧
      (A ∩ Xn = ∅ ↔ I = ∅) ∧ (A \ Xn = ∅ ↔ J = ∅) ∧ I ∪ J = B ∧ I ∩ J = ∅ := by
  by_cases h1 : A ∩ Xn = ∅
  · refine ⟨∅, B, Or.inl rfl, hBE, by simp [h1], ?_, by simp, by simp⟩
    have hAeq : A \ Xn = A := by
      ext x
      simp only [Set.mem_sdiff]
      refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxn => ?_⟩⟩
      exact Set.eq_empty_iff_forall_notMem.mp h1 x ⟨hx, hxn⟩
    rw [hAeq, hAB]
  · by_cases h2 : A \ Xn = ∅
    · refine ⟨B, ∅, hBE, Or.inl rfl, ?_, iff_of_true h2 rfl, by simp, by simp⟩
      have hAeq : A ∩ Xn = A := by
        ext x
        simp only [Set.mem_inter_iff]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
        by_contra hxn
        exact Set.eq_empty_iff_forall_notMem.mp h2 x ⟨hx, hxn⟩
      rw [hAeq, hAB]
    · have hAne : A ≠ ∅ := by
        intro hA
        apply h1
        rw [hA]
        exact Set.empty_inter Xn
      have hBne : B ≠ ∅ := fun hB => hAne (hAB.mpr hB)
      have hBE' : E.mem B := hBE.resolve_left hBne
      obtain ⟨Y, Z, hY, hZ, hYne', hZne', hYZinter, hYZunion⟩ := hEnomin hBE'
      have hYne : Y ≠ ∅ := hYne'.ne_empty
      have hZne : Z ≠ ∅ := hZne'.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩

/-- Pad `δ' : Fin n → Bool × Bool` to a total `ℕ → Bool × Bool`, filling positions `≥ n` with
`(true, true)`. -/
def extendTruePair {n : ℕ} (δ' : Fin n → Bool × Bool) : ℕ → Bool × Bool :=
  fun i => (extendTrue (Prod.fst ∘ δ') i, extendTrue (Prod.snd ∘ δ') i)

/-- **Generic "swap-if" disjointness helper**: if `P` and `Q` are disjoint, then choosing `P` for
one Boolean and `Q` for a *different* Boolean always lands in disjoint sets, regardless of which
Boolean is `true`. -/
theorem if_swap_disjoint {γ : Type*} {P Q : Set γ} (hPQ : P ∩ Q = ∅) {b b' : Bool} (hbb' : b ≠ b') :
    (if b then P else Q) ∩ (if b' then P else Q) = ∅ := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> rcases Bool.eq_false_or_eq_true b' with hb' | hb' <;>
    simp_all [Set.inter_comm]

/-- **`NoMinimal` forces `¬ D.mem ∅`, hence every genuine `D`-neighbourhood is non-empty.**
Applying `NoMinimal` at `X := ∅` would demand a non-empty `Y ⊆ Y ∪ Z = ∅`, impossible. (Exercise
8.12(c)(vi)(7): the one fact needed to know `hXmem`/`hYmem`'s enumerated sets are never `∅`, hence
— via the emptiness-transfer already proved in (5)(d) — that their `atomPair`-images `XPseq`/`YPseq`
are never `∅` either, i.e. always *genuine* neighbourhoods on the other side, no extra "extension"
hypothesis needed.) -/
theorem NeighborhoodSystem.NoMinimal.mem_ne_empty {α : Type*} {D : NeighborhoodSystem α}
    (hD : D.NoMinimal) {X : Set α} (hX : D.mem X) : X ≠ ∅ := by
  intro hXe
  subst hXe
  obtain ⟨Y, Z, -, -, hYne, -, -, hunion⟩ := hD hX
  exact hYne.ne_empty (Set.union_empty_iff.mp hunion).1

/-- Restrict `δ : ℕ → Bool × Bool` to `Fin n → Bool × Bool`. -/
def restrictFinPair (δ : ℕ → Bool × Bool) (n : ℕ) : Fin n → Bool × Bool := fun i => δ i.val

theorem extendTruePair_restrictFinPair_agree (δ : ℕ → Bool × Bool) (n i : ℕ) (hi : i < n) :
    extendTruePair (restrictFinPair δ n) i = δ i := by
  have h1 : extendTrue (Prod.fst ∘ restrictFinPair δ n) i = (δ i).1 :=
    extendTrue_restrictFin_agree (Prod.fst ∘ δ) n i hi
  have h2 : extendTrue (Prod.snd ∘ restrictFinPair δ n) i = (δ i).2 :=
    extendTrue_restrictFin_agree (Prod.snd ∘ δ) n i hi
  show (extendTrue (Prod.fst ∘ restrictFinPair δ n) i, extendTrue (Prod.snd ∘ restrictFinPair δ n) i)
      = δ i
  rw [h1, h2]

open Classical in
/-- **Generalization of `Theorem88.lean`'s `splitChoice`.** -/
noncomputable def splitChoice' {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal)
    (A : Set α) (B : Set γ) (Xn : Set α) : Set γ × Set γ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ E.mem B) then
    ⟨(exists_split' hEnomin h.1 h.2 Xn).choose, (exists_split' hEnomin h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)

theorem splitChoice'_isSplitSpec {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal) :
    SplitSpec' (α := α) E (splitChoice' E hEnomin) := by
  intro A B hAB hBE Xn
  classical
  unfold splitChoice'
  rw [dite_eq_left ⟨hAB, hBE⟩]
  exact (exists_split' hEnomin hAB hBE Xn).choose_spec.choose_spec

def xyStep {α γ : Type*} (split : Set α → Set γ → Set α → Set γ × Set γ)
    (A : Set α) (B : Set γ) (Xn : Set α) (b : Bool) : Set α × Set γ :=
  (if b then A ∩ Xn else A \ Xn, if b then (split A B Xn).1 else (split A B Xn).2)

/-- **`xyStep`'s two outputs, at two *different* sign bits, are pairwise disjoint** — the local,
one-step content behind `atomPair`'s eventual pairwise-disjointness invariant. -/
theorem xyStep_disjoint_of_ne {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xyStep split A B Xn b).1 ∩ (xyStep split A B Xn b').1 = ∅ ∧
      (xyStep split A B Xn b).2 ∩ (xyStep split A B Xn b').2 = ∅ :=
  ⟨if_swap_disjoint (by
      ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]; tauto)
      hbb',
    if_swap_disjoint (hsplit hAB hBE Xn).2.2.2.2.2 hbb'⟩

namespace diff
open NeighborhoodSystem

theorem mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hdiff : D.DiffClosed)
    {A B : Set γ} (hA : A = ∅ ∨ D.mem A) (hB : D.mem B) : A \ B = ∅ ∨ D.mem (A \ B) := by
  rcases hA with rfl | hA
  · exact Or.inl (Set.empty_sdiff B)
  · exact hdiff hA hB

end diff
namespace union
open NeighborhoodSystem

/-- **Union-closure from `IsPositive` + `DiffClosed` alone**: if `X` and `Y` are each mem-or-∅ in a
Positive, difference-closed `D`, so is `X ∪ Y`. -/
theorem mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {X Y : Set γ} (hX : X = ∅ ∨ D.mem X) (hY : Y = ∅ ∨ D.mem Y) :
    X ∪ Y = ∅ ∨ D.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · simpa using hY
  · rcases hY with rfl | hY
    · simpa using Or.inr hX
    · set M := D.master with hMdef
      have hXM : X ⊆ M := D.sub_master hX
      have hYM : Y ⊆ M := D.sub_master hY
      rcases hdiff D.master_mem hX with hMX0 | hMXm
      · refine Or.inr ?_
        have hXeqM : X = M := Set.Subset.antisymm hXM (Set.sdiff_eq_empty.mp hMX0)
        rw [Set.Subset.antisymm (Set.union_subset hXM hYM) (hXeqM ▸ Set.subset_union_left)]
        exact D.master_mem
      · rcases hdiff D.master_mem hY with hMY0 | hMYm
        · refine Or.inr ?_
          have hYeqM : Y = M := Set.Subset.antisymm hYM (Set.sdiff_eq_empty.mp hMY0)
          rw [Set.Subset.antisymm (Set.union_subset hXM hYM) (hYeqM ▸ Set.subset_union_right)]
          exact D.master_mem
        · have eq_master : X ∪ Y = M \ ((M \ X) ∩ (M \ Y)) := by
            ext x
            have hXx : x ∈ X → x ∈ M := @hXM x
            have hYx : x ∈ Y → x ∈ M := @hYM x
            simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
            tauto
          rw [eq_master]
          rcases Set.eq_empty_or_nonempty ((M \ X) ∩ (M \ Y)) with hcap0 | hcapne
          · rw [hcap0, Set.sdiff_empty]; exact Or.inr D.master_mem
          · exact hdiff D.master_mem ((hpos hMXm hMYm).mpr hcapne)

end union
open NeighborhoodSystem

/-- **`Fintype`-indexed union-closure from `IsPositive` + `DiffClosed` alone**, generalizing
`Definition87.lean`'s `U.iUnion_mem`/`Exercise812.lean`'s `V_iUnion_mem` to an abstract `D`. Proved
identically (fold `union.mem_or_empty` over `Finset.univ`), just with the generic one-step lemma in
place of `U`/`V`'s hardcoded binary-union facts. -/
theorem iUnion_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {ι : Type*} [Fintype ι] {f : ι → Set γ}
    (hf : ∀ i, f i = ∅ ∨ D.mem (f i)) : (⋃ i, f i) = ∅ ∨ D.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ D.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact union.mem_or_empty hpos hdiff (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall]
  exact hstep Finset.univ

/-- **The `X`-sub-step**, as an instance of `xyStep`: split `D₁`'s side while directly refining
`D₀`'s side. -/
noncomputable def xStep {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep (splitChoice' D₁ hD₁nomin) A B Xn b

namespace xStep
open NeighborhoodSystem

/-- **`xStep`'s `α`-side output is always a subset of `A`** (unconditional: `A ∩ Xn` and `A \ Xn`
are both `⊆ A`). -/
theorem fst_subset {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, ite_true]; exact Set.inter_subset_left
  · simp only [xStep, xyStep, hb]; exact Set.sdiff_subset

/-- **`xStep`'s `β`-side output is a subset of `B`**, given the `SplitSpec'` preconditions
(`I ∪ J = B`, so both `I ⊆ B` and `J ⊆ B`). -/
theorem snd_subset {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).2 ⊆ B := by
  have hspec := splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, ite_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStep, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

/-- **`xStep`'s two outputs, at two different sign bits, are pairwise disjoint.** -/
theorem disjoint_of_ne {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xStep D₁ hD₁nomin A B Xn b).1 ∩ (xStep D₁ hD₁nomin A B Xn b').1 = ∅ ∧
      (xStep D₁ hD₁nomin A B Xn b).2 ∩ (xStep D₁ hD₁nomin A B Xn b').2 = ∅ :=
  xyStep_disjoint_of_ne (splitChoice'_isSplitSpec D₁ hD₁nomin) hAB hBmem Xn hbb'

end xStep
open NeighborhoodSystem

/-- **The `Y`-sub-step**, symmetric to `xStep`: split `D₀`'s side while directly refining `D₁`'s
side. The `.swap` puts the output back into `(α-side, β-side)` order, matching `atomPair`'s own
`(A2, B2)` convention (`xyStep`'s first component is always the *direct* side, which for the
`Y`-sub-step is the `β`-side). -/
noncomputable def yStep {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep (splitChoice' D₀ hD₀nomin) B1 A1 Yn b).swap

namespace yStep
open NeighborhoodSystem

/-- **`yStep`'s two outputs, at two different sign bits, are pairwise disjoint.** -/
theorem disjoint_of_ne {α β : Type*} {D₀ : NeighborhoodSystem α} (hD₀nomin : D₀.NoMinimal)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    {b b' : Bool} (hbb' : b ≠ b') :
    (yStep D₀ hD₀nomin A1 B1 Yn b).1 ∩ (yStep D₀ hD₀nomin A1 B1 Yn b').1 = ∅ ∧
      (yStep D₀ hD₀nomin A1 B1 Yn b).2 ∩ (yStep D₀ hD₀nomin A1 B1 Yn b').2 = ∅ := by
  have h := xyStep_disjoint_of_ne (splitChoice'_isSplitSpec D₀ hD₀nomin) hBA hAmem Yn hbb'
  exact ⟨h.2, h.1⟩

/-- **`yStep`'s `α`-side output is a subset of `A1`**, given the `SplitSpec'` preconditions. -/
theorem fst_subset {α β : Type*} {D₀ : NeighborhoodSystem α} (hD₀nomin : D₀.NoMinimal)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    (b : Bool) : (yStep D₀ hD₀nomin A1 B1 Yn b).1 ⊆ A1 := by
  have hspec := splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem Yn
  by_cases hb : b = true
  · simp only [yStep, xyStep, Prod.swap, hb, ite_true]
    exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [yStep, xyStep, Prod.swap, hb]
    exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

/-- **`yStep`'s `β`-side output is always a subset of `B1`** (unconditional). -/
theorem snd_subset {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStep D₀ hD₀nomin A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStep, xyStep, Prod.swap, hb, ite_true]; exact Set.inter_subset_left
  · simp only [yStep, xyStep, Prod.swap, hb]; exact Set.sdiff_subset

end yStep
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

open Classical in
/-- **The interleaved two-sided atom pair**, depth `n`, sign sequence `δ`. See the section
docstring for the two sub-steps making up each `n → n + 1` transition. -/
noncomputable def atomPair (δ : ℕ → Bool × Bool) : ℕ → Set α × Set β
  | 0 => (D₀.master, D₁.master)
  | (n + 1) =>
      let A := (atomPair δ n).1
      let B := (atomPair δ n).2
      let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
      let A1 := if (δ n).1 then A ∩ X n else A \ X n
      let B1 := if (δ n).1 then IJ1.1 else IJ1.2
      let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
      let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
      let A2 := if (δ n).2 then IJ2.1 else IJ2.2
      (A2, B2)

end AtomPair
end

namespace atomPair
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- Extending/changing `δ` at or beyond position `n` does not change `atomPair δ n` (mirrors
`Theorem88.lean`'s `atomU_congr`/`genAtom_congr`; needs no invariant, since every step is an
ordinary function of its inputs). -/
theorem congr {δ δ' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n = atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n =
        atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn : δ n = δ' n := h n (Nat.lt_succ_self n)
    show
      (let A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
       let B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2
       let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        (let A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1
         let B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2
         let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
         let A1 := if (δ' n).1 then A ∩ X n else A \ X n
         let B1 := if (δ' n).1 then IJ1.1 else IJ1.2
         let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
         let B2 := if (δ' n).2 then B1 ∩ Y n else B1 \ Y n
         let A2 := if (δ' n).2 then IJ2.1 else IJ2.2
         (A2, B2))
    rw [hprev, hn]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The core invariant of the two-sided back-and-forth construction**: at every depth `n` and for
every sign sequence `δ`, the matched pair `atomPair δ n` (a) has matching emptiness
(`= ∅ ↔ = ∅`) and (b)/(c) is mem-or-∅ on each respective side. Proved by a single induction,
alternating the two Boolean-closure/`exists_split'` steps described in the section docstring. -/
theorem invariant (δ : ℕ → Bool × Bool) :
    ∀ n, ((atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 = ∅ ↔
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 = ∅) ∧
      ((atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 = ∅ ∨
        D₀.mem (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1) ∧
      ((atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 = ∅ ∨
        D₁.mem (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inr D₀.master_mem, Or.inr D₁.master_mem⟩
    show (D₀.master = ∅ ↔ D₁.master = ∅)
    exact ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihAB, ihA, ihB⟩ := ih
    set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
    set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
    have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin ihAB ihB (X n)
    set I1 := (splitChoice' D₁ hD₁nomin A B (X n)).1 with hI1def
    set J1 := (splitChoice' D₁ hD₁nomin A B (X n)).2 with hJ1def
    set A1 := (if (δ n).1 then A ∩ X n else A \ X n) with hA1def
    set B1 := (if (δ n).1 then I1 else J1) with hB1def
    have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hB1def, hδ1, ite_true]; exact hspec1.2.2.1
      · simp only [hA1def, hB1def, hδ1]; exact hspec1.2.2.2.1
    have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hδ1, ite_true]; exact inter.mem_or_empty hD₀pos ihA (hXmem n)
      · simp only [hA1def, hδ1]; exact diff.mem_or_empty hD₀diff ihA (hXmem n)
    have hB1mem : B1 = ∅ ∨ D₁.mem B1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hB1def, hδ1, ite_true]; exact hspec1.1
      · simp only [hB1def, hδ1]; exact hspec1.2.1
    have hspec2 := splitChoice'_isSplitSpec D₀ hD₀nomin hA1B1.symm hA1mem (Y n)
    set I2 := (splitChoice' D₀ hD₀nomin B1 A1 (Y n)).1 with hI2def
    set J2 := (splitChoice' D₀ hD₀nomin B1 A1 (Y n)).2 with hJ2def
    set B2 := (if (δ n).2 then B1 ∩ Y n else B1 \ Y n) with hB2def
    set A2 := (if (δ n).2 then I2 else J2) with hA2def
    have hB2A2 : B2 = ∅ ↔ A2 = ∅ := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hA2def, hδ2, ite_true]; exact hspec2.2.2.1
      · simp only [hB2def, hA2def, hδ2]; exact hspec2.2.2.2.1
    have hB2mem : B2 = ∅ ∨ D₁.mem B2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hδ2, ite_true]; exact inter.mem_or_empty hD₁pos hB1mem (hYmem n)
      · simp only [hB2def, hδ2]; exact diff.mem_or_empty hD₁diff hB1mem (hYmem n)
    have hA2mem : A2 = ∅ ∨ D₀.mem A2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hA2def, hδ2, ite_true]; exact hspec2.1
      · simp only [hA2def, hδ2]; exact hspec2.2.1
    show (A2 = ∅ ↔ B2 = ∅) ∧ (A2 = ∅ ∨ D₀.mem A2) ∧ (B2 = ∅ ∨ D₁.mem B2)
    exact ⟨hB2A2.symm, hA2mem, hB2mem⟩

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

/-- **`atomPair`'s recursive step, rephrased as `yStep ∘ xStep`.** Definitionally equal to
`atomPair`'s own `let`-chain (both sides unfold to the identical `(A2, B2)` pair), but stated in
terms of the two named sub-steps so later lemmas can manipulate them algebraically instead of
re-deriving the unfolding by hand. -/
theorem succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) :
    atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1) =
      yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) (δ n).2 := rfl

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`atomPair`'s `β`-side only shrinks from depth `n` to `n + 1`.** -/
theorem snd_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).2 ⊆
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 := by
  rw [atomPair.succ_eq]
  obtain ⟨ihAB, -, ihB⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStep.snd_subset D₀ hD₀nomin _ _ (Y n) (δ n).2).trans
    (xStep.snd_subset hD₁nomin ihAB ihB (X n) (δ n).1)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`atomPair`'s `β`-side is always `⊆ D₁.master`**, symmetric to `atomPair.fst_subset_master`. -/
theorem snd_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ⊆ D₁.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPair.snd_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

end AtomPair
end

end atomPair
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

open Classical in
/-- **`XPseq`**: the union, over all depth-`n` histories, of the `D₁`-piece chosen by the
`X`-sub-step's "+" branch against `X n`. Recovers `X n`'s correspondent on `D₁`'s side (the
two-sided, half-step analogue of `Theorem88.lean`'s `Yseq`). -/
noncomputable def XPseq (n : ℕ) : Set β :=
  ⋃ δ' : Fin n → Bool × Bool,
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2

end AtomPair
end

namespace XPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`XPseq n` is always `∅` or a genuine `D₁`-neighbourhood.** -/
theorem empty_or_mem (n : ℕ) :
    XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ ∨ D₁.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  apply iUnion_mem_or_empty hD₁pos hD₁diff
  intro δ'
  obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n
  exact (splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem (X n)).1

end AtomPair
end

end XPseq
namespace xStep
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`xStep`'s output satisfies the preconditions `yStep` needs** (the `SplitSpec'` hypotheses,
transported across the `X`-sub-step): the `β`-side output is empty iff the `α`-side output is, and
the `α`-side output is mem-or-∅ for `D₀`. Proved exactly as the corresponding step inside
`atomPair.invariant`'s induction (Boolean-closure for the *direct* side, `SplitSpec'` for the
*split* side). -/
theorem spec (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 = ∅ ↔
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 = ∅) ∧
      ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 = ∅ ∨
        D₀.mem (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin ihAB ihB (X n)
  refine ⟨?_, ?_⟩
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStep, xyStep, hδ1, ite_true]; exact hspec1.2.2.1.symm
    · simp only [xStep, xyStep, hδ1]; exact hspec1.2.2.2.1.symm
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStep, xyStep, hδ1, ite_true]; exact inter.mem_or_empty hD₀pos ihA (hXmem n)
    · simp only [xStep, xyStep, hδ1]; exact diff.mem_or_empty hD₀diff ihA (hXmem n)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`xStep.spec_bit`** (8.12(c)(vi)(4)(c)): a drop-in generalization of `xStep.spec` to an
*arbitrary* bit `bx`, not just `δ n`'s own first component — the `SplitSpec'` preconditions `yStep`
needs, transported across the `X`-sub-step at bit `bx`, for *any* history `δ`. Proved by
transporting `xStep.spec` itself across a `Function.update`-adjusted history `δ''` that agrees with
`δ` below `n` and has `(δ'' n).1 = bx` exactly — the two-sided analogue of `Theorem88.lean`'s
`Function.update`-based `δ2` device in `split_fst_eq_inter_Yseq`. -/
theorem spec_bit (δ : ℕ → Bool × Bool) (n : ℕ) (bx : Bool) :
    ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).2 = ∅ ↔
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 = ∅) ∧
      ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 = ∅ ∨
        D₀.mem (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1) := by
  set δ'' := Function.update (extendTruePair (restrictFinPair δ n)) n (bx, true) with hδ''def
  have hagree : ∀ i < n, δ'' i = δ i := by
    intro i hi
    have h1 : δ'' i = (extendTruePair (restrictFinPair δ n)) i := by
      simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
    rw [h1]; exact extendTruePair_restrictFinPair_agree δ n i hi
  have hbit : (δ'' n).1 = bx := by simp [hδ''def]
  have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ'' n =
      atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n := atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
  have hspec := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne δ'' n
  rwa [hcongr, hbit] at hspec

end AtomPair
end

end xStep
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

open Classical in
/-- **`YPseq`** (8.12(c)(vi)(4)(b)): the union, over all depth-`n` histories *and* a free `Bool`
`bx` for position `n`'s `X`-sub-step bit, of the `D₀`-piece chosen by the `Y`-sub-step's "+" branch
against `Y n`. Recovers `Y n`'s correspondent on `D₀`'s side. -/
noncomputable def YPseq (n : ℕ) : Set α :=
  ⋃ (δ' : Fin n → Bool × Bool) (bx : Bool),
    (yStep D₀ hD₀nomin
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) bx).1
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) bx).2
      (Y n) true).1

end AtomPair
end

namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`YPseq n` is always `∅` or a genuine `D₀`-neighbourhood.** -/
theorem empty_or_mem (n : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ ∨ D₀.mem (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  apply iUnion_mem_or_empty hD₀pos hD₀diff
  intro δ'
  apply iUnion_mem_or_empty hD₀pos hD₀diff
  intro bx
  obtain ⟨hBA, hAmem⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n bx
  exact splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem (Y n) |>.1

end AtomPair
end

end YPseq
namespace atomPair
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`atomPair`'s `α`-side only shrinks from depth `n` to `n + 1`.** -/
theorem fst_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).1 ⊆
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 := by
  rw [atomPair.succ_eq]
  obtain ⟨hspecAB, hspecAmem⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStep.fst_subset hD₀nomin hspecAB hspecAmem (Y n) (δ n).2).trans
    (xStep.fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`atomPair`'s `α`-side is always `⊆ D₀.master`** (by induction from the base case
`atomPair δ 0 = D₀.master`, shrinking at each step via `atomPair.fst_subset`). Placed here
(rather than alongside 8.12(c)(vi)(5)'s other consumers below) since 8.12(c)(vi)(5)(a)'s
`xStep.snd_succ_eq`/`yStep.fst_succ_eq` closed forms need it too, and both only depend on
`atomPair.fst_subset`/`atomPair.snd_subset` just above — no need to wait for `atomPair.disjoint`
or `XPseq`/`YPseq`. -/
theorem fst_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ⊆ D₀.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPair.fst_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Pairwise disjointness of `atomPair` on both sides at once** (Exercise 8.12(c)(v)): for sign
sequences `δ`, `δ'` disagreeing somewhere below depth `n`, the two matched pairs are disjoint on
*both* the `α`-side and the `β`-side. Proved by induction on `n`, mirroring `Theorem88.lean`'s
`atomU_invariant`'s disjointness clause: the "disagree below `n`" case shrinks via
`atomPair.fst_subset`/`atomPair.snd_subset`; the "agree below `n`, disagree at `n`" case splits on
*which* sub-step first disagrees — the `X`-sub-step (`xStep.disjoint_of_ne` directly, then
`yStep.fst_subset`/`yStep.snd_subset` carry the disjointness through the following `Y`-sub-step),
or the `Y`-sub-step (`atomPair.succ_eq` unifies both `xStep` applications via `hpairEq`/`h1`, then
`yStep.disjoint_of_ne` finishes directly). -/
theorem disjoint (δ δ' : ℕ → Bool × Bool) :
    ∀ n, (∃ i < n, δ i ≠ δ' i) →
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ∩
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1 = ∅ ∧
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 = ∅ := by
  intro n
  induction n with
  | zero => rintro ⟨i, hi, -⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rintro ⟨i, hi, hine⟩
    by_cases hagree : ∀ j < n, δ j = δ' j
    · -- Disagreement is exactly at position `n`: both depth-`n` pairs coincide.
      have hδn : δ n ≠ δ' n := by
        intro heq
        exact hine (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hagree i hi'
          · exact heq)
      have hpairEq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      have hAB' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1 =
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ∧
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 =
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 :=
        ⟨(congrArg Prod.fst hpairEq).symm, (congrArg Prod.snd hpairEq).symm⟩
      by_cases h1 : (δ n).1 = (δ' n).1
      · -- Agree on the `X`-sub-step: the `xStep` application is *literally the same* for `δ`,
        -- `δ'`, so disjointness comes purely from the `Y`-sub-step (which must then disagree).
        have h2 : (δ n).2 ≠ (δ' n).2 := fun h2eq => hδn (Prod.ext_iff.mpr ⟨h1, h2eq⟩)
        rw [atomPair.succ_eq, atomPair.succ_eq, hAB'.1, hAB'.2, h1]
        obtain ⟨hspecAB, hspecAmem⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        rw [h1] at hspecAB hspecAmem
        exact yStep.disjoint_of_ne hD₀nomin hspecAB hspecAmem (Y n) h2
      · -- Disagree already at the `X`-sub-step: the two `xStep` applications are disjoint
        -- outright, and both `yStep` outputs shrink into their respective `xStep` halves.
        obtain ⟨ihAB, ihA, ihB⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStep.disjoint_of_ne hD₁nomin ihAB ihB (X n) h1
        obtain ⟨hspecAB, hspecAmem⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        obtain ⟨hspecAB', hspecAmem'⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ' n
        have h1sub : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).1 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 := by
          rw [atomPair.succ_eq]; exact yStep.fst_subset hD₀nomin hspecAB hspecAmem (Y n) (δ n).2
        have h2sub : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).2 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 := by
          rw [atomPair.succ_eq]; exact yStep.snd_subset D₀ hD₀nomin _ _ (Y n) (δ n).2
        have h1sub' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).1 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 (X n) (δ' n).1).1 := by
          rw [atomPair.succ_eq]; exact yStep.fst_subset hD₀nomin hspecAB' hspecAmem' (Y n) (δ' n).2
        have h2sub' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).2 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 (X n) (δ' n).1).2 := by
          rw [atomPair.succ_eq]; exact yStep.snd_subset D₀ hD₀nomin _ _ (Y n) (δ' n).2
        rw [hAB'.1, hAB'.2] at h1sub' h2sub'
        exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1sub h1sub') hxdisj.1,
          Set.subset_eq_empty (Set.inter_subset_inter h2sub h2sub') hxdisj.2⟩
    · -- Disagreement is somewhere below `n`: shrink via `atomPair.fst_subset`/`atomPair.snd_subset`.
      push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      obtain ⟨hd1, hd2⟩ := ih ⟨j, hj, hjne⟩
      have h1 : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).1 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 := atomPair.fst_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h1' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).1 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1 := atomPair.fst_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ' n
      have h2 : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).2 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 := atomPair.snd_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h2' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).2 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 := atomPair.snd_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ' n
      exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1 h1') hd1,
        Set.subset_eq_empty (Set.inter_subset_inter h2 h2') hd2⟩

end AtomPair
end

end atomPair
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- The interleaved family testing `D₀`'s side: at even positions, `X`'s own enumeration; at odd
positions, `YPseq`'s recovered `D₀`-side pieces. -/
noncomputable def combinedX (n : ℕ) : Set α :=
  if n % 2 = 0 then X (n / 2) else YPseq D₀ D₁ hD₀nomin hD₁nomin X Y (n / 2)

end AtomPair
end

namespace combinedX
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem even (k : ℕ) : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y (2 * k) = X k := by
  unfold combinedX
  rw [ite_eq_left (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem odd (k : ℕ) :
    combinedX D₀ D₁ hD₀nomin hD₁nomin X Y (2 * k + 1) = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  unfold combinedX
  rw [ite_eq_right (by omega : ¬ (2 * k + 1) % 2 = 0), show (2 * k + 1) / 2 = k from by omega]

end AtomPair
end

end combinedX
namespace subset
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem XPseq {n : ℕ} (δ' : Fin n → Bool × Bool) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2 ⊆
      _root_.DomainTheory.NeighbourhoodSystems.XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
  Set.subset_iUnion
    (fun δ' => (xStep D₁ hD₁nomin
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2) δ'

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem YPseq {n : ℕ} (δ' : Fin n → Bool × Bool) (bx : Bool) :
    (yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) bx).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) bx).2
        (Y n) true).1 ⊆ _root_.DomainTheory.NeighbourhoodSystems.YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  intro z hz
  exact Set.mem_iUnion.mpr ⟨δ', Set.mem_iUnion.mpr ⟨bx, hz⟩⟩

end AtomPair
end

end subset
namespace XPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`XPseq n` is always `⊆ D₁.master`.** -/
theorem subset_master (n : ℕ) : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ⊆ D₁.master := by
  apply Set.iUnion_subset
  intro δ'
  exact (xStep.snd_subset hD₁nomin
    (atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (extendTruePair δ') n).1
    (atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (extendTruePair δ') n).2.2 (X n) true).trans
    (atomPair.snd_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (extendTruePair δ') n)

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hX0 in
/-- **Exercise 8.12(c)(vii)(2).** `XPseq 0 = D₁.master` (Scott's `X 0 = D₀.master`/`Y 0 = D₁.master`
convention transfers to `atomPair`'s `D₁`-side image), mirroring `Theorem88.lean`'s
`Yseq_zero_eq_master`: unfolding one step of the two-sided recursion at `n = 0`, `atomPair`'s own
`0`-clause is `(D₀.master, D₁.master)` regardless of the sign sequence, so the `X`-sub-step's split
against `X 0 = D₀.master` puts everything into the "+"-branch on both outputs (the "−"-branch
`D₀.master \ D₀.master = ∅` is forced empty by `SplitSpec'`), and `I ∪ J = D₁.master` with `J = ∅`
forces `I = D₁.master`. -/
theorem zero : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y 0 = D₁.master := by
  apply Set.Subset.antisymm
    (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne 0)
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin hAB1 hBE1 (X 0)
  have hdiff1 : D₀.master \ X 0 = ∅ := by rw [hX0]; exact Set.sdiff_self
  have h2empty1 : (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).2 = ∅ :=
    hspec1.2.2.2.1.mp hdiff1
  have hunion1 := hspec1.2.2.2.2.1
  rw [h2empty1, Set.union_empty] at hunion1
  have hkey : D₁.master ⊆ (xStep D₁ hD₁nomin D₀.master D₁.master (X 0) true).2 := by
    show D₁.master ⊆ (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).1
    rw [hunion1]
  exact hkey.trans (subset.XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (Fin.elim0 : Fin 0 → Bool × Bool))

end Iso
end

end XPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- The interleaved family testing `D₁`'s side: at even positions, `XPseq`'s recovered `D₁`-side
pieces; at odd positions, `Y`'s own enumeration. -/
noncomputable def combinedY (n : ℕ) : Set β :=
  if n % 2 = 0 then XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (n / 2) else Y (n / 2)

end AtomPair
end

namespace combinedY
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem even (k : ℕ) :
    combinedY D₀ D₁ hD₀nomin hD₁nomin X Y (2 * k) = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  unfold combinedY
  rw [ite_eq_left (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k from by omega]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem odd (k : ℕ) : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y (2 * k + 1) = Y k := by
  unfold combinedY
  rw [ite_eq_right (by omega : ¬ (2 * k + 1) % 2 = 0), show (2 * k + 1) / 2 = k from by omega]

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- `combinedY i` is always `⊆ D₁.master`, symmetric to `combinedX.subset_master`: at even
positions it is `XPseq (i/2)`, already known `⊆ D₁.master`; at odd positions it is `Y (i/2)`, a
`D₁.mem` set (via `D₁.sub_master`). -/
theorem subset_master (i : ℕ) :
    combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₁.master := by
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi
  · rw [show i = 2 * (i / 2) from by omega, combinedY.even]
    exact XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (i / 2)
  · rw [show i = 2 * (i / 2) + 1 from by omega, combinedY.odd]
    exact D₁.sub_master (hYmem (i / 2))

end AtomPair
end

end combinedY
namespace xStep
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The "I-formula" for `XPseq`**: the `D₁`-piece chosen by the depth-`n` `X`-sub-step's "+"
branch (for *any* history `δ`) is exactly the intersection of `atomPair δ n`'s `D₁`-side with
`XPseq n`. Mirrors `Theorem88.lean`'s `split_fst_eq_inter_Yseq`, but proved directly against
`atomPair`'s own invariants (no `atomE`/`genAtom` involved — see the section docstring above). -/
theorem snd_eq_inter_XPseq (δ : ℕ → Bool × Bool) (n : ℕ) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) true).2 =
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  set I := (xStep D₁ hD₁nomin A B (X n) true).2 with hIdef
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := xStep.snd_subset hD₁nomin hAB hBmem (X n) true
    have hIsubX : I ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
      have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y
          (extendTruePair (restrictFinPair δ n)) n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y
          (fun i hi => extendTruePair_restrictFinPair_agree δ n i hi)
      have hmem := subset.XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (restrictFinPair δ n)
      rwa [hcongr] at hmem
    exact Set.subset_inter hIsubB hIsubX
  · rintro z ⟨hzB, hzX⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzX
    by_cases hagree : ∀ i < n, extendTruePair δ' i = δ i
    · have hABeq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      rwa [hABeq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hdisjBB := (atomPair.disjoint D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') δ n ⟨j, hj, hjne⟩).2
      obtain ⟨hAB', -, hBmem'⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
        hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n
      have hzB' : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 :=
        xStep.snd_subset hD₁nomin hAB' hBmem' (X n) true hz'
      exact absurd (Set.mem_inter hzB' hzB) (by rw [hdisjBB]; simp)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Two-branch closed form for the `X`-sub-step's `D₁`-side output** (Exercise 8.12(c)(vi)(5)(a)):
completes `xStep.snd_eq_inter_XPseq`'s `true`-only I-formula into a full `genAtom`-shaped recursive
step at *either* sign, mirroring `Theorem88.lean`'s `atomU_succ_eq` exactly — the `false` branch is
derived algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = B`/`I ∩ J = ∅`, with no
new disjointness or invariant content. -/
theorem snd_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) b).2 =
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩
        (if b then XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n
          else D₁.master \ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  set XP := XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n with hXPdef
  have hspec := splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem (X n)
  have hIeq : (xStep D₁ hD₁nomin A B (X n) true).2 = B ∩ XP :=
    xStep.snd_eq_inter_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne δ n
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hIeq
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (xStep D₁ hD₁nomin A B (X n) false).2 = B \ XP := by
      have hunion : (xStep D₁ hD₁nomin A B (X n) true).2 ∪ (xStep D₁ hD₁nomin A B (X n) false).2
          = B := by simp only [xStep, xyStep]; exact hspec.2.2.2.2.1
      have hinter : (xStep D₁ hD₁nomin A B (X n) true).2 ∩ (xStep D₁ hD₁nomin A B (X n) false).2
          = ∅ := by simp only [xStep, xyStep]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ B := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxXP => ?_⟩
        have hxI : x ∈ (xStep D₁ hD₁nomin A B (X n) true).2 := hIeq ▸ Set.mem_inter hxB hxXP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnXP⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ B ∩ XP).2 hxnXP
        · exact hxJ
    rw [hJeq]
    have hsub := atomPair.snd_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end AtomPair
end

end xStep
namespace genAtom
open NeighborhoodSystem

/-- **`genAtom`'s own recursive equation, as a rewritable lemma** (mirrors `Theorem88.lean`'s
`atomU_succ`; `genAtom`'s `def` is a direct structural match on its `Nat` argument, so this holds by
`rfl`, but stating it separately lets `rw` fire on `Nat`-literal successor forms like `2 * n + 1 + 1`
without needing to unfold `genAtom` itself). -/
theorem succ' {γ : Type*} (Z : ℕ → Set γ) (M : Set γ) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ (n + 1) = genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n) := rfl

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The odd-depth half-step identity for `combinedX`**: given `atomPair δ n`'s `α`-side agrees
with `genAtom combinedX` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `Y`-sub-step's own (choice-split) `α`-side output — via (vi)(5)(a)'s closed form
`yStep.fst_succ_eq`, run at `combinedδ`/`combinedY`'s odd value `(δ n).2`. -/
theorem combinedX_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 =
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n)) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n + 1) =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 := by
  rw [genAtom.succ', ← hn, combinedδ_even, combinedX.even]
  have hAsub : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ⊆ D₀.master :=
    atomPair.fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne δ n
  simp only [xStep, xyStep]
  rcases Bool.eq_false_or_eq_true (δ n).1 with hb | hb
  · simp only [hb, ite_true]
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact inter.diff_eq_diff_of_subset hAsub

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The odd-depth half-step identity for `combinedY`**: given `atomPair δ n`'s `β`-side agrees
with `genAtom combinedY` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own (choice-split) `β`-side output — via (vi)(5)(a)'s closed form
`xStep.snd_succ_eq`, run at `combinedδ`/`combinedX`'s even value `(δ n).1`. -/
theorem combinedY_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 =
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n)) :
    genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n + 1) =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 := by
  rw [genAtom.succ', ← hn, combinedδ_even, combinedY.even]
  exact (xStep.snd_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne δ n (δ n).1).symm

end AtomPair
end

end genAtom
namespace yStep
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The "I-formula" for `YPseq`** (8.12(c)(vi)(4)(d)): the `D₀`-piece chosen by the `Y`-sub-step's
"+" branch (applied to the post-`X`-sub-step values at *any* history `δ`'s own bit `(δ n).1`) is
exactly the intersection of that post-`X`-sub-step `D₀`-value with `YPseq n`. Mirrors
`xStep.snd_eq_inter_XPseq`, but needs `xStep.spec_bit`'s bridge (unlike `XPseq`'s proof) to handle
the `⊇` direction's "history agrees below `n` but the union's bit differs from `(δ n).1`" case. -/
theorem fst_eq_inter_YPseq (δ : ℕ → Bool × Bool) (n : ℕ) :
    (yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) true).1 =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 ∩
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  obtain ⟨hBA, hAmem⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne δ n (δ n).1
  set A1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 with hA1def
  set B1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 with hB1def
  set J := (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 with hJdef
  apply Set.Subset.antisymm
  · have hJsubA1 : J ⊆ A1 := yStep.fst_subset hD₀nomin hBA hAmem (Y n) true
    have hJsubY : J ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
      have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y
          (extendTruePair (restrictFinPair δ n)) n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y
          (fun i hi => extendTruePair_restrictFinPair_agree δ n i hi)
      have hmem := subset.YPseq D₀ D₁ hD₀nomin hD₁nomin X Y (restrictFinPair δ n) (δ n).1
      rwa [hcongr] at hmem
    exact Set.subset_inter hJsubA1 hJsubY
  · rintro z ⟨hzA1, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    obtain ⟨bx, hz''⟩ := Set.mem_iUnion.mp hz'
    by_cases hagree : ∀ i < n, extendTruePair δ' i = δ i
    · have hABeq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair.congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      by_cases hbxeq : bx = (δ n).1
      · rw [hABeq, hbxeq] at hz''
        exact hz''
      · obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStep.disjoint_of_ne hD₁nomin hAB hBmem (X n) hbxeq
        rw [hABeq] at hz''
        have hzA1' : z ∈ (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) bx).1 := by
          obtain ⟨hBA', hAmem'⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
            hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n bx
          exact yStep.fst_subset hD₀nomin hBA' hAmem' (Y n) true hz''
        exact absurd (Set.mem_inter hzA1' hzA1) (by rw [hxdisj.1]; simp)
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hdisjAA := (atomPair.disjoint D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') δ n ⟨j, hj, hjne⟩).1
      have hzA1' : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1 := by
        obtain ⟨hBA', hAmem'⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n bx
        have hJ'subA1' := yStep.fst_subset hD₀nomin hBA' hAmem' (Y n) true hz''
        exact xStep.fst_subset D₁ hD₁nomin _ _ (X n) bx hJ'subA1'
      have hzAfull : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 :=
        xStep.fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1 hzA1
      exact absurd (Set.mem_inter hzA1' hzAfull) (by rw [hdisjAA]; simp)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Two-branch closed form for the `Y`-sub-step's `D₀`-side output** (Exercise 8.12(c)(vi)(5)(a)):
completes `yStep.fst_eq_inter_YPseq`'s `true`-only I-formula into a full `genAtom`-shaped recursive
step at *either* sign of the `Y`-sub-step itself (the `X`-sub-step's own bit stays fixed at `(δ
n).1`, exactly as in `yStep.fst_eq_inter_YPseq` — no `xStep.spec_bit`-style further generalization
is needed here, since 8.12(c)(vi)(5)(b)'s combined-family recursion only ever calls this at `δ`'s
own bit). Mirrors `xStep.snd_succ_eq` above (equivalently `Theorem88.lean`'s `atomU_succ_eq`), with
the `false` branch derived algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = B`/
`I ∩ J = ∅`. -/
theorem fst_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) b).1 =
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 ∩
        (if b then YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n
          else D₀.master \ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) := by
  obtain ⟨hBA, hAmem⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne δ n
  set A1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 with hA1def
  set B1 := (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 with hB1def
  set YP := YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n with hYPdef
  have hspec := splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem (Y n)
  have hJeqTrue : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 = A1 ∩ YP :=
    yStep.fst_eq_inter_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne δ n
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hJeqTrue
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (yStep D₀ hD₀nomin A1 B1 (Y n) false).1 = A1 \ YP := by
      have hunion : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 ∪ (yStep D₀ hD₀nomin A1 B1 (Y n) false).1
          = A1 := by simp only [yStep, xyStep, Prod.swap]; exact hspec.2.2.2.2.1
      have hinter : (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 ∩ (yStep D₀ hD₀nomin A1 B1 (Y n) false).1
          = ∅ := by simp only [yStep, xyStep, Prod.swap]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxA1 : x ∈ A1 := hunion ▸ Or.inr hxJ
        refine ⟨hxA1, fun hxYP => ?_⟩
        have hxI : x ∈ (yStep D₀ hD₀nomin A1 B1 (Y n) true).1 := hJeqTrue ▸ Set.mem_inter hxA1 hxYP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxA1, hxnYP⟩
        rw [← hunion] at hxA1
        rcases hxA1 with hxI | hxJ
        · exact absurd (hJeqTrue ▸ hxI : x ∈ A1 ∩ YP).2 hxnYP
        · exact hxJ
    rw [hJeq]
    have hsub : A1 ⊆ D₀.master := (xStep.fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1).trans
      (atomPair.fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne δ n)
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end AtomPair
end

end yStep
namespace atomPair
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Headline closed form, `β`-side** (Exercise 8.12(c)(vi)(5)(b)), symmetric to
`atomPair.fst_eq_genAtom`: `atomPair δ n`'s `β`-side coincides with `genAtom` over the interleaved
family `combinedY` at depth `2 * n`, via `genAtom.combinedY_succ_eq` ((vi)(5)(a)'s `X`-sub-step
closed form `xStep.snd_succ_eq`) then the `Y`-sub-step's direct `β`-side output (elementary, no
closed form needed — it is literally `if (δ n).2 then B1 ∩ Y n else B1 \ Y n` by `yStep`'s own
definition). -/
theorem snd_eq_genAtom (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 =
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom.combinedY_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne δ n hIH
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPair.succ_eq, h2, genAtom.succ', combinedδ_odd, combinedY.odd, hodd]
      obtain ⟨hAB, -, hBmem⟩ := atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
        hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have hB1sub := (xStep.snd_subset hD₁nomin hAB hBmem (X n) (δ n).1).trans
        (atomPair.snd_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne δ n)
      simp only [yStep, xyStep, Prod.swap]
      rcases Bool.eq_false_or_eq_true (δ n).2 with hb | hb
      · simp only [hb, ite_true]
      · simp only [hb, Bool.false_eq_true, ite_false]
        exact (inter.diff_eq_diff_of_subset hB1sub).symm

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **Headline closed form, `α`-side** (Exercise 8.12(c)(vi)(5)(b)): `atomPair δ n`'s `α`-side
coincides with `genAtom` over the interleaved family `combinedX` at the doubled depth `2 * n`.
Proved by induction on `n`, each step performing the two half-step rewrites
`genAtom.combinedX_succ_eq` (`X`-sub-step half, elementary) then `yStep.fst_succ_eq` ((vi)(5)(a)'s
`Y`-sub-step closed form) — mirrors `Theorem88.lean`'s one-line `atomU_eq_genAtom`, just with each
level's step split into the two named half-steps. -/
theorem fst_eq_genAtom (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 =
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master (combinedδ δ) (2 * n) := by
  induction n with
  | zero => rfl
  | succ n hIH =>
      have hodd := genAtom.combinedX_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne δ n hIH
      have hstep := yStep.fst_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne δ n (δ n).2
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [atomPair.succ_eq, hstep, h2, genAtom.succ', combinedδ_odd, combinedX.odd, hodd]

end AtomPair
end

end atomPair
namespace hcore
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The even-index case of `hcore`** (Exercise 8.12(c)(vi)(5)(c)(2)): for any `δ' : ℕ → Bool` and
any `n`, `genAtom combinedX δ' (2*n) = ∅ ↔ genAtom combinedY δ' (2*n) = ∅`. Direct instantiation:
de-interleave `δ'` (via (c)(1)), rewrite both `genAtom`s back to `atomPair (deinterleaveδ δ') n`'s
two sides via (b)'s `atomPair.fst_eq_genAtom`/`atomPair.snd_eq_genAtom`, then close with
`atomPair.invariant`'s clause (a) (already `Pass`, (iv)). -/
theorem even (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ' (2 * n) = ∅ ↔
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ' (2 * n) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    ← atomPair.fst_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n,
    ← atomPair.snd_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n]
  exact (atomPair.invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne (deinterleaveδ δ') n).1

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The odd-index case of `hcore`** (Exercise 8.12(c)(vi)(5)(c)(3)): for any `δ' : ℕ → Bool` and
any `n`, `genAtom combinedX δ' (2*n+1) = ∅ ↔ genAtom combinedY δ' (2*n+1) = ∅`. Direct
instantiation: de-interleave `δ'` (via (c)(1)), rewrite both `genAtom`s at the odd depth
`2 * n + 1` down to the `X`-sub-step's own two sides (`(xStep … (deinterleaveδ δ' n).1).1`/`.2`) via
(b)'s odd-depth half-step identities `genAtom.combinedX_succ_eq`/`genAtom.combinedY_succ_eq` (fed
by (b)'s even-depth closed forms `atomPair.fst_eq_genAtom`/`atomPair.snd_eq_genAtom` for their own
`hn` hypotheses), then close directly with `xStep.spec_bit`'s matching-emptiness clause (already
`Pass`, (vi)(4)(c)). -/
theorem odd (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ' (2 * n + 1) = ∅ ↔
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ' (2 * n + 1) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    genAtom.combinedX_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n
      (atomPair.fst_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne (deinterleaveδ δ') n),
    genAtom.combinedY_succ_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne (deinterleaveδ δ') n
      (atomPair.snd_eq_genAtom D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne (deinterleaveδ δ') n)]
  exact (xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
    hD₀mne hD₁mne (deinterleaveδ δ') n ((deinterleaveδ δ') n).1).1.symm

end AtomPair
end

end hcore
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`hcore`** (Exercise 8.12(c)(vi)(5)(c)(4), final assembly): for any `δ' : ℕ → Bool` and any
`n`, `genAtom combinedX δ' n = ∅ ↔ genAtom combinedY δ' n = ∅` — the actual `hcore` hypothesis
`Theorem88.lean`'s `transfer_dir` needs for the interleaved families `combinedX`/`combinedY`. Pure
glue: a parity case split on `n` (via `omega`, not `Nat.even_or_odd`/`Nat.even_or_odd'`, matching
this file's established choice-free-arithmetic style) matching `n = 2 * (n/2)` against (2)'s
`hcore.even` and `n = 2 * (n/2) + 1` against (3)'s `hcore.odd`. -/
theorem hcore (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ' n = ∅ ↔
      genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ' n = ∅ := by
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn | hn
  · rw [show n = 2 * (n / 2) from by omega]
    exact hcore.even D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne δ' (n / 2)
  · rw [show n = 2 * (n / 2) + 1 from by omega]
    exact hcore.odd D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne δ' (n / 2)

end AtomPair
end

namespace transfer
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem empty_combined {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ D₀.master | ∀ p ∈ cs, (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}.Nonempty ↔
      {y ∈ D₁.master |
        ∀ p ∈ cs, (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}.Nonempty := by
  have hc := hcore D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne
  have hc' : ∀ δ n, genAtom (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master δ n = ∅ ↔
      genAtom (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master δ n = ∅ :=
    fun δ n => (hc δ n).symm
  exact ⟨transfer_dir (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master
      (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master hc hn,
    transfer_dir (combinedY D₀ D₁ hD₀nomin hD₁nomin X Y) D₁.master
      (combinedX D₀ D₁ hD₀nomin hD₁nomin X Y) D₀.master hc' hn⟩

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem double_subset_combined (i j k : ℕ) :
    D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have key := transfer.empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ D₀.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j) \ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j) \ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_empty_combined (i j : ℕ) :
    D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j =
        ∅ ↔
      D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j = ∅ := by
  have key := transfer.empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (cs := [(i, true), (j, true)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ D₀.master |
      ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master |
      ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩
          combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem subset_combined (i j : ℕ) :
    D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  have key := transfer.empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ D₀.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ x ∈ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₀.master ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i) \
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y p.1)}
      = (D₁.master ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i) \
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_eq_combined (i j k : ℕ)
    (hi : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₀.master)
    (hk : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ D₀.master) :
    combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j =
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j =
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have h1 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i := by
    have := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
      hXmem hYmem hD₀mne hD₁mne k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedY.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k)] at this
  have h2 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    have := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
      hXmem hYmem hD₀mne hD₁mne k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedY.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k)] at this
  have h3 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    have := transfer.double_subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right
        (combinedY.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne i)] at this
  constructor
  · intro heq
    have hki : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

end AtomPair
end

end transfer
namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`YPseq n` is always `⊆ D₀.master`.** -/
theorem subset_master (n : ℕ) : YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ⊆ D₀.master := by
  apply Set.iUnion_subset
  intro δ'
  apply Set.iUnion_subset
  intro bx
  obtain ⟨hBA, hAmem⟩ := xStep.spec_bit D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n bx
  exact (yStep.fst_subset hD₀nomin hBA hAmem (Y n) true).trans
    ((xStep.fst_subset D₁ hD₁nomin _ _ (X n) bx).trans
      (atomPair.fst_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne (extendTruePair δ') n))

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hX0 hY0 in
/-- **Exercise 8.12(c)(vii)(2), symmetric half.** `YPseq 0 = D₀.master`, by the same `SplitSpec'`
argument applied to the *second* (`Y`-)sub-step, now feeding off `XPseq.zero`'s already-computed
`D₁`-side value at the first sub-step. -/
theorem zero : YPseq D₀ D₁ hD₀nomin hD₁nomin X Y 0 = D₀.master := by
  apply Set.Subset.antisymm
    (YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne 0)
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin hAB1 hBE1 (X 0)
  have hdiff1 : D₀.master \ X 0 = ∅ := by rw [hX0]; exact Set.sdiff_self
  have h2empty1 : (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).2 = ∅ :=
    hspec1.2.2.2.1.mp hdiff1
  have hunion1 := hspec1.2.2.2.2.1
  rw [h2empty1, Set.union_empty] at hunion1
  have hAB2 : D₁.master = ∅ ↔ D₀.master = ∅ := hAB1.symm
  have hBE2 : D₀.master = ∅ ∨ D₀.mem D₀.master := Or.inr D₀.master_mem
  have hspec2 := splitChoice'_isSplitSpec D₀ hD₀nomin hAB2 hBE2 (Y 0)
  have hdiff2 : D₁.master \ Y 0 = ∅ := by rw [hY0]; exact Set.sdiff_self
  have h2empty2 : (splitChoice' D₀ hD₀nomin D₁.master D₀.master (Y 0)).2 = ∅ :=
    hspec2.2.2.2.1.mp hdiff2
  have hunion2 := hspec2.2.2.2.2.1
  rw [h2empty2, Set.union_empty] at hunion2
  have hgoal : (yStep D₀ hD₀nomin (D₀.master ∩ X 0)
      (splitChoice' D₁ hD₁nomin D₀.master D₁.master (X 0)).1 (Y 0) true).1 ⊆
      YPseq D₀ D₁ hD₀nomin hD₁nomin X Y 0 :=
    subset.YPseq D₀ D₁ hD₀nomin hD₁nomin X Y (Fin.elim0 : Fin 0 → Bool × Bool) true
  rw [hunion1, hX0, Set.inter_self] at hgoal
  have hkey2 : D₀.master ⊆ (yStep D₀ hD₀nomin D₀.master D₁.master (Y 0) true).1 := by
    show D₀.master ⊆ (splitChoice' D₀ hD₀nomin D₁.master D₀.master (Y 0)).1
    rw [hunion2]
  exact hkey2.trans hgoal

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(3), cross-parity order fact, other mix.** `YPseq i ⊆ X j ↔
Y i ⊆ XPseq j`: the symmetric specialization of `transfer.subset_combined` at `(2i+1, 2j)`. -/
theorem subset_X_iff_Y_subset_XPseq (i j : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ X j ↔
      Y i ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  have key := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j)
  rw [combinedX.odd, combinedX.even, combinedY.odd, combinedY.even,
    Set.inter_eq_self_of_subset_right
      (YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (hYmem i))] at key
  exact key

end Iso
end

end YPseq
open NeighborhoodSystem

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(3), cross-parity order fact (`even`/`odd` mix).** `X i ⊆ YPseq j ↔
XPseq i ⊆ Y j`: a direct specialization of `transfer.subset_combined` at the mixed indices
`(2i, 2j+1)` (`combinedX`/`combinedY` at an even and an odd index respectively), simplified by the
same `Set.inter_eq_self_of_subset_right` bookkeeping as (5)(d)'s same-parity headline facts. No new
proof machinery — `transfer.subset_combined` already holds for arbitrary index pairs. -/
theorem X_subset_YPseq_iff_XPseq_subset_Y (i j : ℕ) :
    X i ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ Y j := by
  have key := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j + 1)
  rw [combinedX.even, combinedX.odd, combinedY.even, combinedY.odd,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (hXmem i)),
    Set.inter_eq_self_of_subset_right
      (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i)] at key
  exact key

end Iso
end

namespace XPseq
open NeighborhoodSystem

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(4), the cross-parity `embed_eq_iff` analogue.** `XPseq j = Y k ↔
X j = YPseq k`: unlike `Theorem88a.lean`'s single-enumeration `embed_eq_iff` (a direct corollary of
one `embed_subset_iff` applied twice), this two-family version packages **both** cross-parity order
facts from (vii)(3) (`X_subset_YPseq_iff_XPseq_subset_Y` at `(j, k)` and
`YPseq.subset_X_iff_Y_subset_XPseq` at `(k, j)`) via antisymmetry on each side. Needed because
`toD1`/`toD0`'s `up_mem` case must rename a `D₁`-mem (resp. `D₀`-mem) witness produced by
`hYcover`/`hXcover` as some `Y k`/`X k` back into the `XPseq`/`YPseq` "coordinates" that the filter
`x`/`y` actually testifies about. -/
theorem eq_Y_iff_X_eq_YPseq (j k : ℕ) :
    XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = Y k ↔ X j = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne j k).mpr h.subset)
      ((YPseq.subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne k j).mpr h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne j k).mp h.subset)
      ((YPseq.subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne k j).mp h.symm.subset)

end Iso
end

end XPseq
namespace combinedX
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- `combinedX i` is always `⊆ D₀.master`: at even positions it is `X (i/2)`, a `D₀.mem` set
(via `D₀.sub_master`); at odd positions it is `YPseq (i/2)`, already known `⊆ D₀.master`. -/
theorem subset_master (i : ℕ) :
    combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₀.master := by
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with hi | hi
  · rw [show i = 2 * (i / 2) from by omega, combinedX.even]
    exact D₀.sub_master (hXmem (i / 2))
  · rw [show i = 2 * (i / 2) + 1 from by omega, combinedX.odd]
    exact YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (i / 2)

end AtomPair
end

end combinedX
namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_eq_iff_Y_inter_eq (i j k : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      Y i ∩ Y j = Y k := by
  have key := transfer.inter_eq_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j + 1) (2 * k + 1)
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * i + 1))
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * k + 1))
  rw [combinedX.odd, combinedX.odd, combinedX.odd, combinedY.odd, combinedY.odd,
    combinedY.odd] at key
  exact key

end AtomPair
end

end YPseq
open NeighborhoodSystem

namespace XPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem X_inter_empty_iff_XPseq_inter_empty (i j : ℕ) :
    X i ∩ X j = ∅ ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = ∅ := by
  have key := transfer.inter_empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j)
  rw [combinedX.even, combinedX.even, combinedY.even, combinedY.even,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (hXmem i)),
    Set.inter_eq_self_of_subset_right
      (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i)] at key
  exact key

theorem X_eq_empty_iff_XPseq_eq_empty (n : ℕ) :
    X n = ∅ ↔ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ := by
  have := X_inter_empty_iff_XPseq_inter_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne n n
  rwa [Set.inter_self, Set.inter_self] at this

theorem ne_empty (n : ℕ) : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ≠ ∅ := fun h =>
  hD₀nomin.mem_ne_empty (hXmem n)
    ((X_eq_empty_iff_XPseq_eq_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne n).mpr h)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`XPseq n` is always a genuine `D₁`-neighbourhood** (never merely `∅`-or-`mem`): the actual
"other side" of `X n`. -/
theorem mem (n : ℕ) : D₁.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) :=
  (XPseq.empty_or_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne n).resolve_left
    (XPseq.ne_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n)

end AtomPair
end

end XPseq
open NeighborhoodSystem

namespace YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem inter_empty_iff_Y_inter_empty (i j : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = ∅ ↔
      Y i ∩ Y j = ∅ := by
  have key := transfer.inter_empty_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j + 1)
  rw [combinedX.odd, combinedX.odd, combinedY.odd, combinedY.odd,
    Set.inter_eq_self_of_subset_right
      (YPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (hYmem i))] at key
  exact key

theorem Y_eq_empty_iff_YPseq_eq_empty (n : ℕ) :
    Y n = ∅ ↔ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = ∅ := by
  have := inter_empty_iff_Y_inter_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne n n
  rw [Set.inter_self, Set.inter_self] at this
  exact this.symm

theorem ne_empty (n : ℕ) : YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ≠ ∅ := fun h =>
  hD₁nomin.mem_ne_empty (hYmem n)
    ((Y_eq_empty_iff_YPseq_eq_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
      hYmem hD₀mne hD₁mne n).mpr h)

end AtomPair
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **`YPseq n` is always a genuine `D₀`-neighbourhood**, symmetric to `XPseq.mem`. -/
theorem mem (n : ℕ) : D₀.mem (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n) :=
  (YPseq.empty_or_mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne n).resolve_left
    (YPseq.ne_empty D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n)

end AtomPair
end

end YPseq
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem X_subset_iff_XPseq_subset (i j : ℕ) :
    X i ⊆ X j ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  have key := transfer.subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j)
  rw [combinedX.even, combinedX.even, combinedY.even, combinedY.even,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (hXmem i)),
    Set.inter_eq_self_of_subset_right
      (XPseq.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i)] at key
  exact key

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- **Exercise 8.12(c)(vii)(6), the same-family `embed_eq_iff` companion.** `X i = X j ↔
XPseq i = XPseq j`, needed by `domainIso812c`'s `map_rel_iff'`. Unlike `up_mem`'s two-*family* renaming
(needing (4)'s `XPseq.eq_Y_iff_X_eq_YPseq`), `map_rel_iff'` only ever compares two `XPseq`-indices
against each other, so the ordinary same-family pattern — `X_subset_iff_XPseq_subset` applied in
each direction, packaged via `Set.Subset.antisymm` — suffices, exactly as `Theorem88a.lean`'s own
`embed_eq_iff` (single index family). -/
theorem X_eq_iff_XPseq_eq (i j : ℕ) :
    X i = X j ↔ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne i j).mp h.subset)
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j i).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne i j).mpr h.subset)
      ((X_subset_iff_XPseq_subset D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j i).mpr h.symm.subset)

end Iso
end

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem X_inter_eq_iff_XPseq_inter_eq (i j k : ℕ) :
    X i ∩ X j = X k ↔
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have key := transfer.inter_eq_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i) (2 * j) (2 * k)
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * i))
    (combinedX.subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
      hD₀mne hD₁mne (2 * k))
  rw [combinedX.even, combinedX.even, combinedX.even, combinedY.even, combinedY.even,
    combinedY.even] at key
  exact key

end AtomPair
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hXcover in
/-- **Exercise 8.12(c)(vii)(3), `exists_inter_index` (`D₀ → D₁` direction).** Given a `D₀`-side
witness that `X i ∩ X j` is itself a neighbourhood, `hXcover` names it as some `X m`, and (5)(d)'s
`X_inter_eq_iff_XPseq_inter_eq` pushes the same equation across to `XPseq`. Direct transcription of
`Theorem88a.lean`'s `exists_inter_index_of_dmem`. -/
theorem exists_inter_index_X {i j : ℕ} (hDij : D₀.mem (X i ∩ X j)) :
    ∃ m, X i ∩ X j = X m ∧
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        XPseq D₀ D₁ hD₀nomin hD₁nomin X Y m := by
  obtain ⟨m, hm⟩ := (hXcover (X i ∩ X j)).mp hDij
  exact ⟨m, hm, (X_inter_eq_iff_XPseq_inter_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne i j m).mp hm⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne hYcover in
/-- **Exercise 8.12(c)(vii)(3), `exists_inter_index` (`D₁ → D₀` direction).** Symmetric to
`exists_inter_index_X`, using `hYcover` and `YPseq.inter_eq_iff_Y_inter_eq`. -/
theorem exists_inter_index_Y {i j : ℕ} (hDij : D₁.mem (Y i ∩ Y j)) :
    ∃ m, Y i ∩ Y j = Y m ∧
      YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j =
        YPseq D₀ D₁ hD₀nomin hD₁nomin X Y m := by
  obtain ⟨m, hm⟩ := (hYcover (Y i ∩ Y j)).mp hDij
  exact ⟨m, hm, (YPseq.inter_eq_iff_Y_inter_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne i j m).mpr hm⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(5).** `toD0 : D₁.Element → D₀.Element`, the pullback filter
`{S | ∃ n, S = YPseq n ∧ y.mem (Y n)}` — exact mirror of `toD1` with the two sides' roles swapped
(`YPseq.mem`/`YPseq.zero`/`exists_inter_index_Y` for `sub`/`master_mem`/`inter_mem`;
`YPseq.subset_X_iff_Y_subset_XPseq`/`hXcover`/`hYcover`/`XPseq.eq_Y_iff_X_eq_YPseq` for `up_mem`). -/
def toD0 (y : D₁.Element) : D₀.Element where
  mem S := ∃ n, S = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ∧ y.mem (Y n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ YPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n
  master_mem := ⟨0, (YPseq.zero D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne hX0 hY0).symm, by rw [hY0]; exact y.master_mem⟩
  inter_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    obtain ⟨m, hYeq, hYPeq⟩ := exists_inter_index_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
      hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hYcover (y.sub (y.inter_mem hyi hyj))
    exact ⟨m, hYPeq, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ hD0S2 hS1S2
    obtain ⟨k, hk⟩ := (hXcover S2).mp hD0S2
    subst hk
    have hYi_sub : Y i ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k :=
      (YPseq.subset_X_iff_Y_subset_XPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne i k).mp hS1S2
    have hyXPk : y.mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k) :=
      y.up_mem hyi
        (XPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne k)
        hYi_sub
    obtain ⟨j, hj⟩ := (hYcover (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y k)).mp (y.sub hyXPk)
    have hYPj_eq_Xk : X k = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j :=
      (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne k j).mp hj
    exact ⟨j, hYPj_eq_Xk, hj ▸ hyXPk⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(4).** `toD1 : D₀.Element → D₁.Element`, the pushforward filter
`{T | ∃ n, T = XPseq n ∧ x.mem (X n)}` — direct transcription of `Theorem88a.lean`'s `toDprimeU`.
`sub`/`master_mem`/`inter_mem` are immediate from `XPseq.mem`/`XPseq.zero`/`exists_inter_index_X`
exactly as there; `up_mem` is the one genuinely two-sided step: given `x.mem (X i)` and a `D₁.mem`
target `T₂ ⊇ XPseq i`, `hYcover` names `T₂` as some `Y k`, the cross-parity order fact
`X_subset_YPseq_iff_XPseq_subset_Y` turns `XPseq i ⊆ Y k` into `X i ⊆ YPseq k`, `x.up_mem` (on the
`D₀`-side, using `YPseq.mem`) then gives `x.mem (YPseq k)`, `hXcover` renames `YPseq k` as some
`X j`, and `XPseq.eq_Y_iff_X_eq_YPseq` finally certifies `Y k = XPseq j`. -/
def toD1 (x : D₀.Element) : D₁.Element where
  mem T := ∃ n, T = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n ∧ x.mem (X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ XPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
      hD₁mne n
  master_mem := ⟨0, (XPseq.zero D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
    hYmem hD₀mne hD₁mne hX0).symm, by rw [hX0]; exact x.master_mem⟩
  inter_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hXeq, hXPeq⟩ := exists_inter_index_X D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
      hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hXcover (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hXPeq, hXeq ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ hD1T2 hT1T2
    obtain ⟨k, hk⟩ := (hYcover T2).mp hD1T2
    subst hk
    have hXi_sub : X i ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k :=
      (X_subset_YPseq_iff_XPseq_subset_Y D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
        hXmem hYmem hD₀mne hD₁mne i k).mpr hT1T2
    have hxYPk : x.mem (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k) :=
      x.up_mem hxi
        (YPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne k)
        hXi_sub
    obtain ⟨j, hj⟩ := (hXcover (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y k)).mp (x.sub hxYPk)
    have hXPj_eq_Yk : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y j = Y k :=
      (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne j k).mpr hj.symm
    exact ⟨j, hXPj_eq_Yk.symm, hj ▸ hxYPk⟩

end Iso
end

section
section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

/-- **Exercise 8.12(c)(vii)(6), final assembly.** The order isomorphism `D₀.Element ≃o D₁.Element`.
`toD1`/`toD0` are mutually inverse (via (4)'s `XPseq.eq_Y_iff_X_eq_YPseq`, resolving which index in
the *other* family represents a given neighbourhood) and preserve/reflect `≤` (via
`X_eq_iff_XPseq_eq`) — direct transcription of `Theorem88a.lean`'s `domainIso`, generalized from one
shared index family (`e`/`Yidx`) to genuinely two (`X`/`XPseq` and `Y`/`YPseq`). -/
noncomputable def domainIso812c : DomainIso D₀ D₁ where
  toFun := toD1 D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne
    hXcover hYcover hX0
  invFun := toD0 D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne hXcover hYcover hX0 hY0
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      have hXeq : X k = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k n).mp hk.symm
      rw [hn, ← hXeq]
      exact hxk
    · intro hS
      obtain ⟨m, hm⟩ := (hXcover S).mp (x.sub hS)
      have hxXm : x.mem (X m) := hm ▸ hS
      obtain ⟨n, hn⟩ := (hYcover (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y m)).mp
        (XPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne m)
      have hSYPn : S = YPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        hm.trans ((XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
          X Y hXmem hYmem hD₀mne hD₁mne m n).mp hn)
      exact ⟨n, hSYPn, m, hn.symm, hxXm⟩
  right_inv y := by
    apply Element.ext
    intro T
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      have hXPeq : XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n = Y k :=
        (XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne n k).mpr hk
      rw [hn, hXPeq]
      exact hyk
    · intro hT
      obtain ⟨m, hm⟩ := (hYcover T).mp (y.sub hT)
      have hyYm : y.mem (Y m) := hm ▸ hT
      obtain ⟨n, hn⟩ := (hXcover (YPseq D₀ D₁ hD₀nomin hD₁nomin X Y m)).mp
        (YPseq.mem D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
          hD₁mne m)
      have hTXPn : T = XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
        hm.trans (((XPseq.eq_Y_iff_X_eq_YPseq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne n m).mpr hn.symm).symm)
      exact ⟨n, hTXPn, m, hn.symm, hyYm⟩
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hXcover S).mp (x.sub hxS)
      have hxn : x.mem (X n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _
        (⟨n, rfl, hxn⟩ : (toD1 D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne hXcover hYcover hX0 x).mem (XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n))
      rw [hn, (X_eq_iff_XPseq_eq D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
        hYmem hD₀mne hD₁mne n k).mpr hk]
      exact hx2k
    · intro hle T hT
      obtain ⟨n, hn, hxn⟩ := hT
      exact ⟨n, hn, hle _ hxn⟩

end Iso
end

section

/-- **Generalization of `Theorem88.lean`'s `split_fst_subset`**: a splitting operation's first
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_fst_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

/-- **Generalization of `Theorem88.lean`'s `split_snd_subset`**: a splitting operation's second
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_snd_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

end AtomPair

section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hXcover
  hYcover hX0 hY0 in
/-- **Exercise 8.12(c)(vii)(6), headline.** `D₀ ≅ᴰ D₁`: completes Exercise 8.12(c) in full. -/
theorem isomorphic_812c : D₀ ≅ᴰ D₁ :=
  ⟨domainIso812c D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne hXcover hYcover hX0 hY0⟩
end Iso
end

end DomainTheory.NeighbourhoodSystems
end
