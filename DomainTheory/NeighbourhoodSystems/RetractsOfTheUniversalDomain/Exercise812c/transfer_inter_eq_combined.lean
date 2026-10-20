module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_subset_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_double_subset_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

theorem transfer_inter_eq_combined (i j k : ℕ)
    (hi : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ D₀.master)
    (hk : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ D₀.master) :
    combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j =
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j =
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
  have h1 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i := by
    have := transfer_subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
      hXmem hYmem hD₀mne hD₁mne k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedY_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k)] at this
  have h2 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k ⊆ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j := by
    have := transfer_subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
      hXmem hYmem hD₀mne hD₁mne k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedY_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
          hYmem hD₀mne hD₁mne k)] at this
  have h3 : combinedX D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedX D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedX D₀ D₁ hD₀nomin hD₁nomin X Y k ↔
      combinedY D₀ D₁ hD₀nomin hD₁nomin X Y i ∩ combinedY D₀ D₁ hD₀nomin hD₁nomin X Y j ⊆
        combinedY D₀ D₁ hD₀nomin hD₁nomin X Y k := by
    have := transfer_double_subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
      X Y hXmem hYmem hD₀mne hD₁mne i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right
        (combinedY_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem
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

end DomainTheory.NeighbourhoodSystems
