module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableSplit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

noncomputable def atomPairG (δ : ℕ → Bool × Bool) : ℕ → Set α × Set β
  | 0 => (D₀.master, D₁.master)
  | (n + 1) =>
      let A := (atomPairG δ n).1
      let B := (atomPairG δ n).2
      let IJ1 := splitX A B (X n)
      let A1 := if (δ n).1 then A ∩ X n else A \ X n
      let B1 := if (δ n).1 then IJ1.1 else IJ1.2
      let IJ2 := splitY B1 A1 (Y n)
      let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
      let A2 := if (δ n).2 then IJ2.1 else IJ2.2
      (A2, B2)

end AtomPairGen

namespace atomPairG
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

omit hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in

theorem congr {δ δ' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomPairG D₀ D₁ splitY splitX X Y δ n = atomPairG D₀ D₁ splitY splitX X Y δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomPairG D₀ D₁ splitY splitX X Y δ n =
        atomPairG D₀ D₁ splitY splitX X Y δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn : δ n = δ' n := h n (Nat.lt_succ_self n)
    show
      (let A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1
       let B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2
       let IJ1 := splitX A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitY B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        (let A := (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
         let B := (atomPairG D₀ D₁ splitY splitX X Y δ' n).2
         let IJ1 := splitX A B (X n)
         let A1 := if (δ' n).1 then A ∩ X n else A \ X n
         let B1 := if (δ' n).1 then IJ1.1 else IJ1.2
         let IJ2 := splitY B1 A1 (Y n)
         let B2 := if (δ' n).2 then B1 ∩ Y n else B1 \ Y n
         let A2 := if (δ' n).2 then IJ2.1 else IJ2.2
         (A2, B2))
    rw [hprev, hn]

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem invariant (δ : ℕ → Bool × Bool) :
    ∀ n, ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ↔
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ∨
        D₀.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).1) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅ ∨
        D₁.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inr D₀.master_mem, Or.inr D₁.master_mem⟩
    show (D₀.master = ∅ ↔ D₁.master = ∅)
    exact ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihAB, ihA, ihB⟩ := ih
    set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
    have hspec1 := hxSplit ihAB ihB (X n)
    set I1 := (splitX A B (X n)).1 with hI1def
    set J1 := (splitX A B (X n)).2 with hJ1def
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
    have hspec2 := hySplit hA1B1.symm hA1mem (Y n)
    set I2 := (splitY B1 A1 (Y n)).1 with hI2def
    set J2 := (splitY B1 A1 (Y n)).2 with hJ2def
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

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

theorem succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) :
    atomPairG D₀ D₁ splitY splitX X Y δ (n + 1) =
      yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2
        (Y n) (δ n).2 := rfl

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem fst_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).1) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).1) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  have hBAtrue : (xStepG splitX A B (X n) true).2 = ∅ ↔ (xStepG splitX A B (X n) true).1 = ∅ := by
    simp only [xStepG, xyStep, ite_true]; exact hspec1.2.2.1.symm
  have hAmemtrue : (xStepG splitX A B (X n) true).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) true).1 := by
    simp only [xStepG, xyStep, ite_true]; exact inter.mem_or_empty hD₀pos ihA (hXmem n)
  have hBAfalse : (xStepG splitX A B (X n) false).2 = ∅ ↔ (xStepG splitX A B (X n) false).1 = ∅ := by
    simp only [xStepG, xyStep]; exact hspec1.2.2.2.1.symm
  have hAmemfalse : (xStepG splitX A B (X n) false).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) false).1 := by
    simp only [xStepG, xyStep]; exact diff.mem_or_empty hD₀diff ihA (hXmem n)
  rw [yStepG.fst_union hySplit hBAtrue hAmemtrue (Y n),
    yStepG.fst_union hySplit hBAfalse hAmemfalse (Y n)]
  exact xStepG.fst_union splitX A B (X n)

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem master_covered (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).1 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG.fst_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).1 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).1 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagree, atomPairG.succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

end AtomPairGen

section AtomPairGenDelta

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in

theorem master_covered_deltaPair (n : ℕ) :
    ∀ z ∈ D₀.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).1 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG.master_covered D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair.lt _ n, ?_⟩
  rw [atomPairG.congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair.encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

end AtomPairGenDelta

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem snd_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).2 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).2) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).2 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).2) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  rw [yStepG.snd_union splitY (xStepG splitX A B (X n) true).1 (xStepG splitX A B (X n) true).2
      (Y n),
    yStepG.snd_union splitY (xStepG splitX A B (X n) false).1 (xStepG splitX A B (X n) false).2
      (Y n)]
  exact xStepG.snd_union hxSplit ihAB ihB (X n)

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem master_covered_snd (n : ℕ) :
    ∀ z ∈ D₁.master, ∃ δ' : Fin n → Bool × Bool,
      z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') n).2 := by
  induction n with
  | zero => exact fun z hz => ⟨Fin.elim0, hz⟩
  | succ n ih =>
    intro z hz
    obtain ⟨δ'₀, hδ'₀⟩ := ih z hz
    have hcover := atomPairG.snd_union_step D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ'₀) n
    set A := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ'₀) n).2 with hBdef
    have step : ∀ b1 b2 : Bool,
        z ∈ (yStepG splitY (xStepG splitX A B (X n) b1).1 (xStepG splitX A B (X n) b1).2
          (Y n) b2).2 →
        ∃ δ' : Fin (n + 1) → Bool × Bool,
          z ∈ (atomPairG D₀ D₁ splitY splitX X Y (extendTruePair δ') (n + 1)).2 := by
      intro b1 b2 hz'
      set δ'' := Function.update (extendTruePair δ'₀) n (b1, b2) with hδ''def
      refine ⟨restrictFinPair δ'' (n + 1), ?_⟩
      have hagree : ∀ i < n + 1, extendTruePair (restrictFinPair δ'' (n + 1)) i = δ'' i :=
        fun i hi => extendTruePair_restrictFinPair_agree δ'' (n + 1) i hi
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagree, atomPairG.succ_eq]
      have hagreeN : ∀ i < n, δ'' i = extendTruePair δ'₀ i := by
        intro i hi
        simp [hδ''def, Function.update_of_ne (ne_of_lt hi)]
      have hbit : δ'' n = (b1, b2) := by simp [hδ''def]
      rw [atomPairG.congr D₀ D₁ splitY splitX X Y hagreeN, hbit]
      exact hz'
    rw [← hcover] at hδ'₀
    simp only [Set.mem_union] at hδ'₀
    rcases hδ'₀ with (h1 | h2) | (h3 | h4)
    · exact step true true h1
    · exact step true false h2
    · exact step false true h3
    · exact step false false h4

end AtomPairGen

section AtomPairGenDelta

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in

theorem master_covered_deltaPair_snd (n : ℕ) :
    ∀ z ∈ D₁.master, ∃ i < 4 ^ n, z ∈ (atomPairG D₀ D₁ splitY splitX X Y (deltaPair i) n).2 := by
  intro z hz
  obtain ⟨δ', hδ'⟩ := atomPairG.master_covered_snd D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
    hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne n z hz
  refine ⟨encodeDeltaPair (extendTruePair δ') n, encodeDeltaPair.lt _ n, ?_⟩
  rw [atomPairG.congr D₀ D₁ splitY splitX X Y
    (fun i hi => deltaPair.encodeDeltaPair (extendTruePair δ') n i hi)]
  exact hδ'

end AtomPairGenDelta

end atomPairG

namespace xStepG
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem spec (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2 = ∅ ↔
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 = ∅) ∧
      ((xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 = ∅ ∨
        D₀.mem (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  refine ⟨?_, ?_⟩
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStepG, xyStep, hδ1, ite_true]; exact hspec1.2.2.1.symm
    · simp only [xStepG, xyStep, hδ1]; exact hspec1.2.2.2.1.symm
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStepG, xyStep, hδ1, ite_true]; exact inter.mem_or_empty hD₀pos ihA (hXmem n)
    · simp only [xStepG, xyStep, hδ1]; exact diff.mem_or_empty hD₀diff ihA (hXmem n)

end AtomPairGen

end xStepG

namespace atomPairG
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem fst_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  rw [atomPairG.succ_eq]
  obtain ⟨hspecAB, hspecAmem⟩ := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStepG.fst_subset hySplit hspecAB hspecAmem (Y n) (δ n).2).trans
    (xStepG.fst_subset splitX _ _ (X n) (δ n).1)

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem fst_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ⊆ D₀.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPairG.fst_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem snd_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
      (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := by
  rw [atomPairG.succ_eq]
  obtain ⟨ihAB, -, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStepG.snd_subset splitY _ _ (Y n) (δ n).2).trans
    (xStepG.snd_subset hxSplit ihAB ihB (X n) (δ n).1)

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem disjoint (δ δ' : ℕ → Bool × Bool) :
    ∀ n, (∃ i < n, δ i ≠ δ' i) →
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ∩
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 = ∅ ∧
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 ∩
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 = ∅ := by
  intro n
  induction n with
  | zero => rintro ⟨i, hi, -⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rintro ⟨i, hi, hine⟩
    by_cases hagree : ∀ j < n, δ j = δ' j
    · have hδn : δ n ≠ δ' n := by
        intro heq
        exact hine (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hagree i hi'
          · exact heq)
      have hpairEq : atomPairG D₀ D₁ splitY splitX X Y δ n =
          atomPairG D₀ D₁ splitY splitX X Y δ' n :=
        atomPairG.congr D₀ D₁ splitY splitX X Y hagree
      have hAB' : (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 =
          (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ∧
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 =
            (atomPairG D₀ D₁ splitY splitX X Y δ n).2 :=
        ⟨(congrArg Prod.fst hpairEq).symm, (congrArg Prod.snd hpairEq).symm⟩
      by_cases h1 : (δ n).1 = (δ' n).1
      · have h2 : (δ n).2 ≠ (δ' n).2 := fun h2eq => hδn (Prod.ext_iff.mpr ⟨h1, h2eq⟩)
        rw [atomPairG.succ_eq, atomPairG.succ_eq, hAB'.1, hAB'.2, h1]
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        rw [h1] at hspecAB hspecAmem
        exact yStepG.disjoint_of_ne hySplit hspecAB hspecAmem (Y n) h2
      · obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStepG.disjoint_of_ne hxSplit ihAB ihB (X n) h1
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        obtain ⟨hspecAB', hspecAmem'⟩ := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
        have h1sub : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 := by
          rw [atomPairG.succ_eq]; exact yStepG.fst_subset hySplit hspecAB hspecAmem (Y n) (δ n).2
        have h2sub : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2 := by
          rw [atomPairG.succ_eq]; exact yStepG.snd_subset splitY _ _ (Y n) (δ n).2
        have h1sub' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).1 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 (X n) (δ' n).1).1 := by
          rw [atomPairG.succ_eq]; exact yStepG.fst_subset hySplit hspecAB' hspecAmem' (Y n) (δ' n).2
        have h2sub' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).2 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 (X n) (δ' n).1).2 := by
          rw [atomPairG.succ_eq]; exact yStepG.snd_subset splitY _ _ (Y n) (δ' n).2
        rw [hAB'.1, hAB'.2] at h1sub' h2sub'
        exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1sub h1sub') hxdisj.1,
          Set.subset_eq_empty (Set.inter_subset_inter h2sub h2sub') hxdisj.2⟩
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      obtain ⟨hd1, hd2⟩ := ih ⟨j, hj, hjne⟩
      have h1 : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := atomPairG.fst_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h1' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).1 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 := atomPairG.fst_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
      have h2 : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := atomPairG.snd_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h2' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).2 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 := atomPairG.snd_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
      exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1 h1') hd1,
        Set.subset_eq_empty (Set.inter_subset_inter h2 h2') hd2⟩

end AtomPairGen

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

theorem snd_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ n).2 ⊆ D₁.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPairG.snd_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

end AtomPairGen

end atomPairG

namespace atomPairG
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hD₀nomin : D₀.NoMinimal) (hD₁nomin : D₁.NoMinimal)

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₀nomin in

theorem exists_deltaPair_inter_Xn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ∩ P₀.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₀nomin.mem_ne_empty (P₀.mem_X n))
  have hzmaster : z ∈ D₀.master := D₀.sub_master (P₀.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := master_covered_deltaPair D₀ D₁ hD₀pos hD₀diff splitY hySplit
    hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₁nomin in

theorem exists_deltaPair_inter_Yn_ne_empty (n : ℕ) :
    ∃ i < 4 ^ n, (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ∩ P₁.X n ≠ ∅ := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr (hD₁nomin.mem_ne_empty (P₁.mem_X n))
  have hzmaster : z ∈ D₁.master := D₁.sub_master (P₁.mem_X n) hz
  obtain ⟨i, hi, hzcover⟩ := master_covered_deltaPair_snd D₀ D₁ hD₀pos hD₀diff splitY
    hySplit hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne n z hzmaster
  exact ⟨i, hi, Set.nonempty_iff_ne_empty.mp ⟨z, hzcover, hz⟩⟩

end

end atomPairG

end DomainTheory.NeighbourhoodSystems
