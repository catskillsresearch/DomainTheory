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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedXY812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedY812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseq812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.hcore812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.transfer812c

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems
