module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPair812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitSpec812c

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

open Classical in

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
    ·
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
      ·

        have h2 : (δ n).2 ≠ (δ' n).2 := fun h2eq => hδn (Prod.ext_iff.mpr ⟨h1, h2eq⟩)
        rw [atomPair.succ_eq, atomPair.succ_eq, hAB'.1, hAB'.2, h1]
        obtain ⟨hspecAB, hspecAmem⟩ := xStep.spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        rw [h1] at hspecAB hspecAmem
        exact yStep.disjoint_of_ne hD₀nomin hspecAB hspecAmem (Y n) h2
      ·

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
    ·
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

end DomainTheory.NeighbourhoodSystems
