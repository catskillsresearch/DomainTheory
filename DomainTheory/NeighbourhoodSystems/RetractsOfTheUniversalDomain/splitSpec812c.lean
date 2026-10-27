module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

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
`Definition87.lean`'s `U.iUnion_mem`/`Exercise812.lean`'s `V.iUnion_mem` to an abstract `D`. Proved
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

end DomainTheory.NeighbourhoodSystems
