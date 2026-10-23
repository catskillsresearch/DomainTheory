module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtomEmptyChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Difference-closure**, generalizing `U_diff_mem`/`V_diff_mem`: the set-difference of two
neighbourhoods is again a neighbourhood, or empty. -/
def NeighborhoodSystem.DiffClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → X \ Y = ∅ ∨ D.mem (X \ Y)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Atomlessness** ("no minimal neighbourhoods"), generalizing `U_no_minimal`/`V_no_minimal`:
every non-empty neighbourhood splits into two disjoint, non-empty neighbourhood pieces whose union
recovers it. (Phrased with explicit `Nonempty` clauses, equivalent given `Y ∩ Z = ∅`/`Y ∪ Z = X` to
`U_no_minimal`/`V_no_minimal`'s own `Y ≠ X`/`Z ≠ X` phrasing, but directly what `exists_split'`
needs — an *abstract* `D.mem` need not itself carry nonemptiness the way `U.mem`/`V.mem` do.) -/
def NeighborhoodSystem.NoMinimal {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X : Set α}, D.mem X →
    ∃ Y Z : Set α, D.mem Y ∧ D.mem Z ∧ Y.Nonempty ∧ Z.Nonempty ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Pad `δ' : Fin n → Bool × Bool` to a total `ℕ → Bool × Bool`, filling positions `≥ n` with
`(true, true)`. -/
def extendTruePair {n : ℕ} (δ' : Fin n → Bool × Bool) : ℕ → Bool × Bool :=
  fun i => (extendTrue (Prod.fst ∘ δ') i, extendTrue (Prod.snd ∘ δ') i)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Generic "swap-if" disjointness helper**: if `P` and `Q` are disjoint, then choosing `P` for
one Boolean and `Q` for a *different* Boolean always lands in disjoint sets, regardless of which
Boolean is `true`. -/
theorem if_swap_disjoint {γ : Type*} {P Q : Set γ} (hPQ : P ∩ Q = ∅) {b b' : Bool} (hbb' : b ≠ b') :
    (if b then P else Q) ∩ (if b' then P else Q) = ∅ := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> rcases Bool.eq_false_or_eq_true b' with hb' | hb' <;>
    simp_all [Set.inter_comm]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₁pos hD₁diff hD₁nomin hYmem hD₀mne hD₁mne in
theorem X_ne_empty (n : ℕ) : X n ≠ ∅ := hD₀nomin.mem_ne_empty (hXmem n)

end AtomPair

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hXmem hD₀mne hD₁mne in
theorem Y_ne_empty (n : ℕ) : Y n ≠ ∅ := hD₁nomin.mem_ne_empty (hYmem n)

end AtomPair

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Restrict `δ : ℕ → Bool × Bool` to `Fin n → Bool × Bool`. -/
def restrictFinPair (δ : ℕ → Bool × Bool) (n : ℕ) : Fin n → Bool × Bool := fun i => δ i.val

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem extendTruePair_restrictFinPair_agree (δ : ℕ → Bool × Bool) (n i : ℕ) (hi : i < n) :
    extendTruePair (restrictFinPair δ n) i = δ i := by
  have h1 : extendTrue (Prod.fst ∘ restrictFinPair δ n) i = (δ i).1 :=
    extendTrue_restrictFin_agree (Prod.fst ∘ δ) n i hi
  have h2 : extendTrue (Prod.snd ∘ restrictFinPair δ n) i = (δ i).2 :=
    extendTrue_restrictFin_agree (Prod.snd ∘ δ) n i hi
  show (extendTrue (Prod.fst ∘ restrictFinPair δ n) i, extendTrue (Prod.snd ∘ restrictFinPair δ n) i)
      = δ i
  rw [h1, h2]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

open Classical in
/-- **Generalization of `Theorem88.lean`'s `splitChoice`.** -/
noncomputable def splitChoice' {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal)
    (A : Set α) (B : Set γ) (Xn : Set α) : Set γ × Set γ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ E.mem B) then
    ⟨(exists_split' hEnomin h.1 h.2 Xn).choose, (exists_split' hEnomin h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem splitChoice'_isSplitSpec {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal) :
    SplitSpec' (α := α) E (splitChoice' E hEnomin) := by
  intro A B hAB hBE Xn
  classical
  unfold splitChoice'
  rw [dite_eq_left ⟨hAB, hBE⟩]
  exact (exists_split' hEnomin hAB hBE Xn).choose_spec.choose_spec

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

def xyStep {α γ : Type*} (split : Set α → Set γ → Set α → Set γ × Set γ)
    (A : Set α) (B : Set γ) (Xn : Set α) (b : Bool) : Set α × Set γ :=
  (if b then A ∩ Xn else A \ Xn, if b then (split A B Xn).1 else (split A B Xn).2)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`xyStep`'s two outputs, at two *different* sign bits, are pairwise disjoint** — the local,
one-step content behind `atomPair`'s eventual pairwise-disjointness invariant. -/
theorem xyStep_disjoint_of_ne {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xyStep split A B Xn b).1 ∩ (xyStep split A B Xn b').1 = ∅ ∧
      (xyStep split A B Xn b).2 ∩ (xyStep split A B Xn b').2 = ∅ :=
  ⟨if_swap_disjoint (inter.diff_self_eq_empty A Xn) hbb',
    if_swap_disjoint (hsplit hAB hBE Xn).2.2.2.2.2 hbb'⟩

end DomainTheory.NeighbourhoodSystems
