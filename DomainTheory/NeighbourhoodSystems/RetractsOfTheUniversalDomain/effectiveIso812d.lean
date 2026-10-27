module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YFoldInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec812d_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomIdx_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YPseqCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseqCode_more

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


namespace hcoreCode
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 1000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
set_option maxHeartbeats 4000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem even (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master δ'
        (2 * n) = ∅ ↔
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        δ' (2 * n) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    ← atomPairG.fst_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 (deinterleaveδ δ') n,
    ← atomPairG.snd_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 (deinterleaveδ δ') n]
  exact (atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit P₀.X
    P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deinterleaveδ δ') n).1

end CombinedCode

section CombinedCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 1000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
set_option maxHeartbeats 4000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem odd (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master δ'
        (2 * n + 1) = ∅ ↔
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        δ' (2 * n + 1) = ∅ := by
  rw [← combinedδ_deinterleaveδ δ',
    genAtom.combinedXCode_succ_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hUnion0 (deinterleaveδ δ') n
      (atomPairG.fst_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        (deinterleaveδ δ') n),
    genAtom.combinedYCode_succ_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 (deinterleaveδ δ') n
      (atomPairG.snd_eq_genAtomCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1
        (deinterleaveδ δ') n)]
  exact (xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit P₀.X P₁.X
    P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deinterleaveδ δ') n).1.symm

end CombinedCode

end hcoreCode
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 1000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
set_option maxHeartbeats 4000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem hcoreCode (δ' : ℕ → Bool) (n : ℕ) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master δ'
        n = ∅ ↔
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        δ' n = ∅ := by
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn | hn
  · rw [show n = 2 * (n / 2) from by omega]
    exact hcoreCode.even P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
      hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 δ' (n / 2)
  · rw [show n = 2 * (n / 2) + 1 from by omega]
    exact hcoreCode.odd P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
      hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 δ' (n / 2)

end CombinedCode

namespace transfer
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem empty_combinedCode {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ D₀.master | ∀ p ∈ cs,
        (p.2 = true ↔ x ∈ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          p.1)}.Nonempty ↔
      {y ∈ D₁.master | ∀ p ∈ cs,
        (p.2 = true ↔ y ∈ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          p.1)}.Nonempty := by
  have hc := hcoreCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
  have hc' : ∀ δ n,
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
          δ n = ∅ ↔
        genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
          δ n = ∅ :=
    fun δ n => (hc δ n).symm
  exact ⟨transfer_dir (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0)
      D₀.master (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
      hc hn,
    transfer_dir (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1)
      D₁.master (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
      hc' hn⟩

end CombinedCodeTransfer

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem double_subset_combinedCode (i j k : ℕ) :
    D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
  have key := transfer.empty_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (cs := [(i, true), (j, true), (k, false)]) (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ D₀.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        p.1)}
      = (D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
          combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) \
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ y ∈ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        p.1)}
      = (D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) \
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end CombinedCodeTransfer

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem subset_combinedCode (i j : ℕ) :
    D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ↔
      D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
  have key := transfer.empty_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ D₀.master | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ x ∈ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        p.1)}
      = (D₀.master ∩ combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) \
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ D₁.master | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ y ∈ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
        p.1)}
      = (D₁.master ∩ combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) \
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

end CombinedCodeTransfer

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem inter_eq_combinedCode (i j k : ℕ)
    (hi : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ⊆ D₀.master)
    (hk : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆ D₀.master) :
    combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j =
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j =
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
  have h1 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i := by
    have := transfer.subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedYCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          k)] at this
  have h2 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
    have := transfer.subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedYCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          k)] at this
  have h3 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
    have := transfer.double_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right
        (combinedYCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          i)] at this
  constructor
  · intro heq
    have hki : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

end CombinedCodeTransfer

end transfer
namespace YPseqCode
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XYPseqCodeZero

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hX0 hY0 in

theorem zero :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 0) = D₀.master := by
  have hjunk0 := atomPairJunk.zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0
  have hcs := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne 0 0 hjunk0
  have hA0 : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₀.master := hcs.1
  have hB0 : P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := hcs.2
  have hxjunk0 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 = 0 := by
    rw [xPseqAtomJunk.eq, hjunk0, selectFn_zero]
    by_contra hcon
    have hle := emptyInterDec.le_one P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1
    rw [hA0, hX0, Set.inter_self] at hempty
    exact hD₀mne.ne_empty hempty
  have hidxeq : xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 =
      hSplitX.posIdx (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx.eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := hxSplit hAB1 hBE1 D₀.master
  have hdiff1 : D₀.master \ D₀.master = ∅ := Set.sdiff_self
  have h2empty1 : (splitX D₀.master D₁.master D₀.master).2 = ∅ := hspec1.2.2.2.1.mp hdiff1
  have hunion1 : (splitX D₀.master D₁.master D₀.master).1 = D₁.master := by
    have hu := hspec1.2.2.2.2.1
    rwa [h2empty1, Set.union_empty] at hu
  have hne1 : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X 0)).1 ≠ ∅ := by rw [hA0, hB0, hX0, hunion1]; exact hD₁mne.ne_empty
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 hne1
  rw [hA0, hB0, hX0] at hposspec
  have hzeroeq : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := by rw [hidxeq, ← hposspec]; exact hunion1
  have hidx0eq : stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      P₀.inter (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx0_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hinterex : ∃ k, P₀.X k ⊆
      P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) ∩ P₀.X 0 :=
    ⟨atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0, by
      rw [hA0, hX0, Set.inter_self]⟩
  have hidx0set : P₀.X (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY 0 0)) = D₀.master := by
    rw [hidx0eq, P₀.inter_spec hinterex, hA0, hX0, Set.inter_self]
  have hstateIdx1 : stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      0 0) = xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 := rfl
  have hraw : selectFn (stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY 0 0)) 1 (selectFn 1
        (emptyInterDec P₁ (Nat.pair (stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX
          splitY hSplitY 0 0)) 0))
        (IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX
          hSplitX splitY hSplitY 0 0)) 0))) = 0 := by
    have hxjunk0' : stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        0 0) = 0 := hxjunk0
    rw [hxjunk0', selectFn_zero, selectFn_one, hstateIdx1]
    by_contra hcon
    have hle := emptyInterDec.le_one P₁ (Nat.pair
      (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₁ (Nat.pair
        (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec.eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp h1
    rw [hzeroeq, hY0, Set.inter_self] at hempty
    exact hD₁mne.ne_empty hempty
  have hyidx0raw := ySubStep.idx0_eq P₀ P₁ hDiff1 splitY hSplitY (h := hraw)
  rw [selectFn_one, hstateIdx1] at hyidx0raw
  have hyidxeq : yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 1 =
      hSplitY.posIdx (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)) 0 :=
    hyidx0raw
  have hyjunkeq : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 1 = 0 := by
    show stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair 0 (Nat.pair 1
      (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)))) = 0
    rw [ySubStep.junk_eq]; exact hraw
  have hAB2 : D₁.master = ∅ ↔ D₀.master = ∅ := hAB1.symm
  have hBE2 : D₀.master = ∅ ∨ D₀.mem D₀.master := Or.inr D₀.master_mem
  have hspec2 := hySplit hAB2 hBE2 D₁.master
  have hdiff2 : D₁.master \ D₁.master = ∅ := Set.sdiff_self
  have h2empty2 : (splitY D₁.master D₀.master D₁.master).2 = ∅ := hspec2.2.2.2.1.mp hdiff2
  have hunion2 : (splitY D₁.master D₀.master D₁.master).1 = D₀.master := by
    have hu := hspec2.2.2.2.2.1
    rwa [h2empty2, Set.union_empty] at hu
  have hne2 : (splitY
      (P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)))
      (P₁.X 0)).1 ≠ ∅ := by rw [hzeroeq, hidx0set, hY0, hunion2]; exact hD₀mne.ne_empty
  have hposspec2 := hSplitY.posIdx_spec
    (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)) 0 hne2
  rw [hzeroeq, hidx0set, hY0] at hposspec2
  have hyzeroeq : P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 1) =
      D₀.master := by rw [hyidxeq, ← hposspec2]; exact hunion2
  apply Set.Subset.antisymm
  · intro z hz
    rcases (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 0
      z).mp hz with ⟨i, -, -, hzi⟩ | ⟨i, -, -, hzi⟩
    · exact D₀.sub_master
        (yPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i 0) hzi
    · exact D₀.sub_master
        (yPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i 1) hzi
  · intro z hz
    refine (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 0
      z).mpr (Or.inr ⟨0, by norm_num, hyjunkeq, ?_⟩)
    rwa [hyzeroeq]

end XYPseqCodeZero

section CombinedCodeCrossFamily

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem subset_X_iff_Y_subset_XPseqCode (i j : ℕ) :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) ⊆ P₀.X j ↔
      P₁.X i ⊆ P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) := by
  have key := transfer.subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i + 1) (2 * j)
  rw [combinedXCode.odd, combinedXCode.even, combinedYCode.odd, combinedYCode.even,
    Set.inter_eq_self_of_subset_right
      (D₀.sub_master (P₀.mem_X
        (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i))),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (P₁.mem_X i))] at key
  exact key

end CombinedCodeCrossFamily

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem inter_eq_iff_Y_inter_eq (i j k : ℕ) :
    P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i) ∩
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) =
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) ↔
      P₁.X i ∩ P₁.X j = P₁.X k := by
  have key := transfer.inter_eq_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i + 1) (2 * j + 1) (2 * k + 1)
    (combinedXCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (2 * i + 1))
    (combinedXCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      (2 * k + 1))
  rw [combinedXCode.odd, combinedXCode.odd, combinedXCode.odd, combinedYCode.odd,
    combinedYCode.odd, combinedYCode.odd] at key
  exact key

end CombinedCodeTransfer

end YPseqCode
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCodeCrossFamily

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem X_subset_YPseqCode_iff_XPseqCode_subset_Y (i j : ℕ) :
    P₀.X i ⊆ P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j) ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) ⊆ P₁.X j := by
  have key := transfer.subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 (2 * i)
    (2 * j + 1)
  rw [combinedXCode.even, combinedXCode.odd, combinedYCode.even, combinedYCode.odd,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (P₀.mem_X i)),
    Set.inter_eq_self_of_subset_right
      (D₁.sub_master (P₁.mem_X
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i)))] at key
  exact key

end CombinedCodeCrossFamily

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem X_subset_iff_XPseqCode_subset (i j : ℕ) :
    P₀.X i ⊆ P₀.X j ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) ⊆
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) := by
  have key := transfer.subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 (2 * i)
    (2 * j)
  rw [combinedXCode.even, combinedXCode.even, combinedYCode.even, combinedYCode.even,
    Set.inter_eq_self_of_subset_right (D₀.sub_master (P₀.mem_X i)),
    Set.inter_eq_self_of_subset_right
      (D₁.sub_master (P₁.mem_X
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i)))] at key
  exact key

end CombinedCodeTransfer

section XEqIffXPseqCodeEq

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem X_eq_iff_XPseqCode_eq (i j : ℕ) :
    P₀.X i = P₀.X j ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) =
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 i
        j).mp h.subset)
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 j
        i).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 i
        j).mpr h.subset)
      ((X_subset_iff_XPseqCode_subset P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 j
        i).mpr h.symm.subset)

end XEqIffXPseqCodeEq

section CombinedCodeTransfer

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
theorem X_inter_eq_iff_XPseqCode_inter_eq (i j k : ℕ) :
    P₀.X i ∩ P₀.X j = P₀.X k ↔
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i) ∩
          P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) =
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) := by
  have key := transfer.inter_eq_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (2 * i) (2 * j) (2 * k)
    (combinedXCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (2 * i))
    (combinedXCode.subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 (2 * k))
  rw [combinedXCode.even, combinedXCode.even, combinedXCode.even, combinedYCode.even,
    combinedYCode.even, combinedYCode.even] at key
  exact key

end CombinedCodeTransfer

namespace XPseqCode
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XYPseqCodeZero

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hX0 in

theorem zero :
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 0) = D₁.master := by
  have hjunk0 := atomPairJunk.zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0
  have hcs := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne 0 0 hjunk0
  have hA0 : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₀.master := hcs.1
  have hB0 : P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := hcs.2
  have hxjunk0 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 = 0 := by
    rw [xPseqAtomJunk.eq, hjunk0, selectFn_zero]
    by_contra hcon
    have hle := emptyInterDec.le_one P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1
    rw [hA0, hX0, Set.inter_self] at hempty
    exact hD₀mne.ne_empty hempty
  have hidxeq : xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 =
      hSplitX.posIdx (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx.eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := hxSplit hAB1 hBE1 D₀.master
  have hdiff1 : D₀.master \ D₀.master = ∅ := Set.sdiff_self
  have h2empty1 : (splitX D₀.master D₁.master D₀.master).2 = ∅ := hspec1.2.2.2.1.mp hdiff1
  have hunion1 : (splitX D₀.master D₁.master D₀.master).1 = D₁.master := by
    have hu := hspec1.2.2.2.2.1
    rwa [h2empty1, Set.union_empty] at hu
  have hne1 : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X 0)).1 ≠ ∅ := by rw [hA0, hB0, hX0, hunion1]; exact hD₁mne.ne_empty
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 hne1
  rw [hA0, hB0, hX0] at hposspec
  have hzeroeq : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := by rw [hidxeq, ← hposspec]; exact hunion1
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, -, -, hzi⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX
      splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
      hUnion1 0 z).mp hz
    exact D₁.sub_master (xPseqAtomIdx.mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i) hzi
  · intro z hz
    refine (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 0
      z).mpr ⟨0, by norm_num, hxjunk0, ?_⟩
    rwa [hzeroeq]

end XYPseqCodeZero

section CombinedCodeCrossFamily

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem eq_Y_iff_X_eq_YPseqCode (j k : ℕ) :
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) = P₁.X k ↔
      P₀.X j = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 j k).mpr h.subset)
      ((YPseqCode.subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 k j).mpr h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 j k).mp h.subset)
      ((YPseqCode.subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 k j).mp h.symm.subset)

end CombinedCodeCrossFamily

end XPseqCode
namespace toD1Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1CodeUpMem

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem up_mem (x : D₀.Element) {T1 T2 : Set β}
    (h1 : ∃ n, T1 = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
      x.mem (P₀.X n))
    (hD1T2 : D₁.mem T2) (hT1T2 : T1 ⊆ T2) :
    ∃ n, T2 = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
      x.mem (P₀.X n) := by
  obtain ⟨i, rfl, hxi⟩ := h1
  obtain ⟨k, hk⟩ := P₁.surj hD1T2
  subst hk
  have hsub : P₀.X i ⊆
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) :=
    (X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i k).mpr hT1T2
  have hxYk :
      x.mem (P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k)) :=
    x.up_mem hxi
      (YPseqCode.mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 k)
      hsub
  refine ⟨YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k, ?_, hxYk⟩
  exact ((XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) k).mpr rfl).symm

end ToD1CodeUpMem

end toD1Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 in

def toD1Code (x : D₀.Element) : D₁.Element where
  mem T := ∃ n, T = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
    x.mem (P₀.X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ XPseqCode.mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n
  master_mem := ⟨0, (XPseqCode.zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 hX0).symm,
    by rw [hX0]; exact x.master_mem⟩
  inter_mem := by
    rintro T1 T2 ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    have hDmem : D₀.mem (P₀.X i ∩ P₀.X j) := x.sub (x.inter_mem hxi hxj)
    obtain ⟨m, hm⟩ := P₀.surj hDmem
    have hcons : ∃ k, P₀.X k ⊆ P₀.X i ∩ P₀.X j := ⟨m, hm.le⟩
    have hinterEq : P₀.X (P₀.inter i j) = P₀.X i ∩ P₀.X j := P₀.inter_spec hcons
    refine ⟨P₀.inter i j, ?_, ?_⟩
    · exact (X_inter_eq_iff_XPseqCode_inter_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        hUnion1 i j (P₀.inter i j)).mp hinterEq.symm
    · rw [hinterEq]; exact x.inter_mem hxi hxj
  up_mem := toD1Code.up_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 x

end ToD1Code

namespace toD0Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0CodeUpMem

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in

theorem up_mem (y : D₁.Element) {S1 S2 : Set α}
    (h1 : ∃ n, S1 = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
      y.mem (P₁.X n))
    (hD0S2 : D₀.mem S2) (hS1S2 : S1 ⊆ S2) :
    ∃ n, S2 = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
      y.mem (P₁.X n) := by
  obtain ⟨i, rfl, hyi⟩ := h1
  obtain ⟨k, hk⟩ := P₀.surj hD0S2
  subst hk
  have hsub : P₁.X i ⊆
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) :=
    (YPseqCode.subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i k).mp hS1S2
  have hyXk :
      y.mem (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k)) :=
    y.up_mem hyi
      (XPseqCode.mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 k)
      hsub
  refine ⟨XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k, ?_, hyXk⟩
  exact (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    k (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k)).mp rfl

end ToD0CodeUpMem

end toD0Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

def toD0Code (y : D₁.Element) : D₀.Element where
  mem S := ∃ n, S = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ∧
    y.mem (P₁.X n)
  sub := fun ⟨n, hn, _⟩ =>
    hn ▸ YPseqCode.mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n
  master_mem := ⟨0, (YPseqCode.zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hX0 hY0).symm,
    by rw [hY0]; exact y.master_mem⟩
  inter_mem := by
    rintro S1 S2 ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hDmem : D₁.mem (P₁.X i ∩ P₁.X j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hm⟩ := P₁.surj hDmem
    have hcons : ∃ k, P₁.X k ⊆ P₁.X i ∩ P₁.X j := ⟨m, hm.le⟩
    have hinterEq : P₁.X (P₁.inter i j) = P₁.X i ∩ P₁.X j := P₁.inter_spec hcons
    refine ⟨P₁.inter i j, ?_, ?_⟩
    · exact (YPseqCode.inter_eq_iff_Y_inter_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
        hUnion1 i j (P₁.inter i j)).mpr hinterEq.symm
    · rw [hinterEq]; exact y.inter_mem hyi hyj
  up_mem := toD0Code.up_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 y

end ToD0Code

namespace toD0Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0CodeToD1Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem toD1Code (x : D₀.Element) :
    toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
      hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
      (_root_.DomainTheory.NeighbourhoodSystems.toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 x) = x := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨m, hS, n, hmn, hxn⟩
    have hXeq : P₀.X n =
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 m) :=
      (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n
        m).mp hmn.symm
    rw [hS, ← hXeq]
    exact hxn
  · intro hxS
    obtain ⟨n, hn⟩ := P₀.surj (x.sub hxS)
    subst hn
    exact ⟨XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n,
      (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n
        (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)).mp rfl,
      n, rfl, hxS⟩

end ToD0CodeToD1Code

end toD0Code
namespace toD1Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1CodeToD0Code

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem toD0Code (y : D₁.Element) :
    toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
      hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      (_root_.DomainTheory.NeighbourhoodSystems.toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 y) = y := by
  apply Element.ext
  intro T
  constructor
  · rintro ⟨m, hT, n, hmn, hyn⟩
    have hYeq : P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 m) =
        P₁.X n :=
      (XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 m
        n).mpr hmn
    rw [hT, hYeq]
    exact hyn
  · intro hyT
    obtain ⟨n, hn⟩ := P₁.surj (y.sub hyT)
    subst hn
    exact ⟨YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n,
      ((XPseqCode.eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
        (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) n).mpr rfl).symm,
      n, rfl, hyT⟩

end ToD1CodeToD0Code

end toD1Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DomainIsoCode812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

noncomputable def domainIsoCode812d : DomainIso D₀ D₁ where
  toFun := toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
  invFun := toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  left_inv := toD0Code.toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  right_inv := toD1Code.toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := P₀.surj (x.sub hxS)
      subst hn
      obtain ⟨k, hk, hx2k⟩ := hle _
        (⟨n, rfl, hxS⟩ : (toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
          hX0 x).mem
          (P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)))
      rw [(X_eq_iff_XPseqCode_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
        hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 n k).mpr hk]
      exact hx2k
    · intro hle T hT
      obtain ⟨n, hn, hxn⟩ := hT
      exact ⟨n, hn, hle _ hxn⟩

end DomainIsoCode812d

namespace toD0Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD0CodeRelIff

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem rel_iff (m n : ℕ) :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).rel (P₁.X m) (P₀.X n) ↔
    ∃ k, P₀.X n = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) ∧
      P₁.X m ⊆ P₁.X k := by
  show (∃ _ : D₁.mem (P₁.X m),
      (toD0Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
        (D₁.principal (P₁.mem_X m))).mem (P₀.X n)) ↔ _
  simp only [toD0Code, mem_principal]
  constructor
  · rintro ⟨-, k, hk, -, hsub⟩
    exact ⟨k, hk, hsub⟩
  · rintro ⟨k, hk, hsub⟩
    exact ⟨P₁.mem_X m, k, hk, P₁.mem_X k, hsub⟩

end ToD0CodeRelIff

end toD0Code
namespace toD1Code
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1CodeRelIff

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem rel_iff (n m : ℕ) :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).rel
      (P₀.X n) (P₁.X m) ↔
    ∃ k, P₁.X m = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k) ∧
      P₀.X n ⊆ P₀.X k := by
  show (∃ _ : D₀.mem (P₀.X n),
      (toD1Code P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit
        hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
        (D₀.principal (P₀.mem_X n))).mem (P₁.X m)) ↔ _
  simp only [toD1Code, mem_principal]
  constructor
  · rintro ⟨-, k, hk, -, hsub⟩
    exact ⟨k, hk, hsub⟩
  · rintro ⟨k, hk, hsub⟩
    exact ⟨P₀.mem_X n, k, hk, P₀.mem_X k, hsub⟩

end ToD1CodeRelIff

end toD1Code
namespace domainIsoCode812d
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DomainIsoCode812dSymmIsComputableMap

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem symm_isComputableMap :
    ComputableMap P₁ P₀ (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
      hUnion1 hX0 hY0).symm) := by
  constructor
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2
      (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 w.unpair.1)) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      ((primrec.YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
        Nat.Primrec.left)
  have hh : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hA : RecDecidable (fun w : ℕ => P₀.X w.unpair.2.unpair.2 =
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 w.unpair.1)) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₀.eq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hB : RecDecidable (fun w : ℕ => P₁.X w.unpair.2.unpair.1 ⊆ P₁.X w.unpair.1) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₁.incl_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) (hA.and hB).re.proj
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).rel (P₁.X t.unpair.1) (P₀.X t.unpair.2) ↔ _
  rw [toD0Code.rel_iff]
  constructor
  · rintro ⟨k, hk, hsub⟩
    exact ⟨k, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hk, hsub⟩⟩
  · rintro ⟨k, hk⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hk
    exact ⟨k, hk.1, hk.2⟩

end DomainIsoCode812dSymmIsComputableMap

section DomainIsoCode812dIsComputableMap

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem isComputableMap :
    ComputableMap P₀ P₁ (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
      hUnion1 hX0 hY0)) := by
  constructor
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2
      (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 w.unpair.1)) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      ((primrec.XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1).comp
        Nat.Primrec.left)
  have hh : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hA : RecDecidable (fun w : ℕ => P₁.X w.unpair.2.unpair.2 =
      P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 w.unpair.1)) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₁.eq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hB : RecDecidable (fun w : ℕ => P₀.X w.unpair.2.unpair.1 ⊆ P₀.X w.unpair.1) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₀.incl_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) (hA.and hB).re.proj
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).rel
      (P₀.X t.unpair.1) (P₁.X t.unpair.2) ↔ _
  rw [toD1Code.rel_iff]
  constructor
  · rintro ⟨k, hk, hsub⟩
    exact ⟨k, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hk, hsub⟩⟩
  · rintro ⟨k, hk⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hk
    exact ⟨k, hk.1, hk.2⟩

end DomainIsoCode812dIsComputableMap

end domainIsoCode812d
section
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def NeighborhoodSystem.UnionClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → D.mem (X ∪ Y)

section InvMapComp812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem invMap_comp_toMap :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).comp
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)) =
    idMap D₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).toElementMap
    ((ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0)).toElementMap x) = _
  rw [toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply, toElementMap_idMap]

end InvMapComp812d

section ToMapComp812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem toMap_comp_invMap :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).comp
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm) =
    idMap D₁ := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0)).toElementMap
    ((ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).toElementMap y) = _
  rw [toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply, toElementMap_idMap]

end ToMapComp812d

section EffectiveIso812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

noncomputable def effectiveIso812d : EffectiveIso P₀ P₁ where
  toMap := ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)
  invMap := ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
    hY0).symm
  toMap_computable := domainIsoCode812d.isComputableMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
    hUnion1 hX0 hY0
  invMap_computable := domainIsoCode812d.symm_isComputableMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX
    splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
    hUnion0 hUnion1 hX0 hY0
  left_inv := invMap_comp_toMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  right_inv := toMap_comp_invMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0

end EffectiveIso812d

section DomainIsoCode812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hDiff0 hDiff1 hSplitX hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
  hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 in

theorem isomorphic_812d : D₀ ≅ᴰ D₁ :=
  ⟨domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0⟩

end DomainIsoCode812d

section EffectiveIso812d

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hDiff0 hDiff1 hSplitX hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
  hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 in

theorem effectivelyIsomorphic_812d : EffectivelyIsomorphic P₀ P₁ :=
  ⟨effectiveIso812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0⟩
end EffectiveIso812d

end

open Domain.Recursive NeighborhoodSystem

theorem U_union_UX_mem (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨⟨L1, hL1⟩, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨⟨L2, hL2⟩, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨L1 ++ L2, by rw [presentedIntervals.append, hL1, hL2]⟩,
    hne1.mono Set.subset_union_left, Set.union_subset hsub1 hsub2⟩

def VunionRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myLor
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem decodeQPairList_appendListCode (c1 c2 : ℕ) :
    decodeQPairList (appendListCode c1 c2) = decodeQPairList c1 ++ decodeQPairList c2 := by
  unfold decodeQPairList
  rw [appendListCode_eq, List.map_append]

def lowXor (x y : ℕ) : ℕ := (x % 2 + y % 2) % 2

def xorStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2))

def myXor (a b : ℕ) : ℕ :=
  (xorStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

def myAndNot (a b : ℕ) : ℕ := myXor a (myLand a b)

def VdiffRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myAndNot
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

theorem myXor_eq_xor (a b : ℕ) : myXor a b = a ^^^ b := by
  have xor_low_rec : ∀ x y : ℕ, x ^^^ y = 2 * (x / 2 ^^^ y / 2) + lowXor x y := by
    intro x y
    have hdiv : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [← Nat.testBit_add_one, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_add_one,
        Nat.testBit_add_one]
    have hmod : lowXor x y = (x ^^^ y) % 2 := by
      unfold lowXor
      rw [Nat.xor_mod_two_eq]
      exact (Nat.add_mod x y 2).symm
    conv_lhs => rw [← Nat.div_add_mod (x ^^^ y) 2]
    rw [hdiv, hmod]
  have xorStep_iter_spec : ∀ k,
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
      (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
          2 ^ k * (a / 2 ^ k ^^^ b / 2 ^ k) = a ^^^ b := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
        Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
    | succ k ih =>
      obtain ⟨hA, hB, hW, hAcc⟩ := ih
      rw [Function.iterate_succ_apply']
      have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
      have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
      have p11 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
          = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
        unfold xorStep; rw [unpair_pair_fst, unpair_pair_fst]
      have p12 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
          = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
        unfold xorStep; rw [unpair_pair_fst, unpair_pair_snd]
      have p21 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
          = 2 * (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
        unfold xorStep; rw [unpair_pair_snd, unpair_pair_fst]
      have p22 : (xorStep (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
          = (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
            + (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
              * lowXor (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                  (xorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
        unfold xorStep; rw [unpair_pair_snd, unpair_pair_snd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [p21, hW, ← pow_succ']
      · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, xor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
        ring
  unfold myXor
  obtain ⟨_, _, _, hAcc⟩ := xorStep_iter_spec (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

theorem myAndNot_eq (a b : ℕ) : myAndNot a b = a ^^^ (a &&& b) := by
  unfold myAndNot; rw [myXor_eq_xor, myLand_eq_land]

namespace atomPairJunk
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem mono {n k : ℕ}
    (h : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 1) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 1 := by
  have hle := atomPairJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY k (n + 1)
  by_contra hne
  have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 0 := by
    omega
  have := atomPairJunk.eq_zero_of_succ (h := h0)
  omega

end atomPairJunk

open Domain.Recursive

def B812e : ComputableBisection VComputablePresentation where
  left := splitVLeft
  right := splitVRight
  left_primrec := primrec_splitVLeft
  right_primrec := primrec_splitVRight
  disjoint := splitV_disjoint
  union := splitV_union
  left_congr := fun _ _ h => splitVLeft_congr h
  right_congr := fun _ _ h => splitVRight_congr h

def Udiff (n m : ℕ) : ℕ := diffCode (canonCode n) (canonCode m)

theorem U_diff_iff_nonempty (n m : ℕ) :
    (∃ k, UX k = UX n \ UX m) ↔ (UX n \ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact (U_mem_UX k).2.1
  · intro hne
    rcases U.diff_mem (U_mem_UX n) (U_mem_UX m) with hempty | hmem
    · exact absurd hempty hne.ne_empty
    · exact U_surj_UX hmem

namespace Udiff
open Domain.Recursive NeighborhoodSystem

theorem eq_diff (n m : ℕ) :
    presentedIntervals (decodeQPairList (Udiff n m)) = UX n \ UX m := by
  unfold Udiff
  exact presentedIntervals_decodeQPairList_diffCode (canonCode n) (canonCode m)

theorem primrec : Nat.Primrec (fun t : ℕ => Udiff t.unpair.1 t.unpair.2) := by
  unfold Udiff
  exact (primrec_diffCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end Udiff
open Domain.Recursive NeighborhoodSystem

namespace Udiff
open Domain.Recursive NeighborhoodSystem

theorem spec {n m : ℕ} (h : ∃ k, UX k = UX n \ UX m) : UX (Udiff n m) = UX n \ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Udiff n m))) := by
    rw [Udiff.eq_diff]
    obtain ⟨k, hk⟩ := h
    rw [← hk]; exact U_mem_UX k
  show presentedIntervals (decodeQPairList (canonCode (Udiff n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Udiff.eq_diff]

end Udiff
open Domain.Recursive NeighborhoodSystem

def U_isComputableDiff : IsComputableDiff UComputablePresentation where
  diffIdx := Udiff
  diffIdx_primrec := Udiff.primrec
  diffIdx_spec := Udiff.spec
  diff_computable := by
    unfold RecDecidable₂
    refine RecDecidable.of_iff (fun t => ?_)
      (recDecidable_presentedIntervals_nonempty.comp Udiff.primrec)
    show (∃ k, UX k = UX t.unpair.1 \ UX t.unpair.2) ↔ _
    rw [U_diff_iff_nonempty, ← Udiff.eq_diff]

end

end DomainTheory.NeighbourhoodSystems
end
