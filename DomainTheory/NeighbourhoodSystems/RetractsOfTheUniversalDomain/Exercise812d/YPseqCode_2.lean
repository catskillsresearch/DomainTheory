module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_6
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_5
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedXCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedYCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.transfer

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
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
/-- **8.12(d)(5)(a), `Y`-side.** `P₀.X (YPseqCode … 0) = D₀.master`. -/
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
  -- The `D₀`-direct-refine companion value at the same depth/bit-source is also the full master.
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
  -- `stateIdx1` of the incoming `X`-sub-step state is definitionally `xPseqAtomIdx`.
  have hstateIdx1 : stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      0 0) = xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 := rfl
  -- `yPseqAtomState`'s inner `X`-sub-step call at `bx = 1` is definitionally `xPseqAtomState`, so
  -- its own "found" condition reduces to the already-established `hxjunk0`/`hzeroeq`.
  have hraw : selectFn (stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY 0 0)) 1 (selectFn 1
        (emptyInterDec P₁ (Nat.pair (stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX
          splitY hSplitY 0 0)) 0))
        (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX
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

end YPseqCode
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace YPseqCode

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
/-- **Exercise 8.12(d)(5)(c)(ii), cross-parity order fact, other mix.** `P₀.X (YPseqCode … i) ⊆
P₀.X j ↔ P₁.X i ⊆ P₁.X (XPseqCode … j)`: code-level analogue of `Exercise812c.lean`'s
`YPseq.subset_X_iff_Y_subset_XPseq` — the symmetric specialization of
`transfer.subset_combinedCode` at `(2i + 1, 2j)`. -/
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

end YPseqCode
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace YPseqCode

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
end DomainTheory.NeighbourhoodSystems
