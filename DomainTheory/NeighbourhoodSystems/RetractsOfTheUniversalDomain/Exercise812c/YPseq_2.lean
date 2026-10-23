module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace YPseq

open NeighborhoodSystem

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

end YPseq
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace YPseq

open NeighborhoodSystem

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

end YPseq
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace YPseq

open NeighborhoodSystem

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

end AtomPair

end YPseq
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace YPseq

open NeighborhoodSystem

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

end YPseq
end DomainTheory.NeighbourhoodSystems
