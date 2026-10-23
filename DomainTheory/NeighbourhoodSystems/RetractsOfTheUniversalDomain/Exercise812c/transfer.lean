module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.hcore
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace transfer

open NeighborhoodSystem

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

end transfer
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace transfer

open NeighborhoodSystem

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

end transfer
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace transfer

open NeighborhoodSystem

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

end transfer
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace transfer

open NeighborhoodSystem

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

end transfer
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace transfer

open NeighborhoodSystem

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

end transfer
end DomainTheory.NeighbourhoodSystems
