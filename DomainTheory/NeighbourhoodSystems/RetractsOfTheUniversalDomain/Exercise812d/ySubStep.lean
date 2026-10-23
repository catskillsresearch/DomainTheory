module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff1 : IsComputableDiff P₁)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **The `Y`-sub-step.** Symmetric to `xSubStep`: refines `D₁`'s side (`idx1`) directly against
`P₁.X n`, and `D₀`'s side (`idx0`) via the matching branch of the split `hSplitY`. Same packed
argument convention `w = pair n (pair b2 s)`. -/
noncomputable def ySubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b2 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b2 (P₁.inter idx1 n) (hDiff1.diffIdx idx1 n)
  let directEmpty := selectFn b2 (emptyInterDec P₁ (Nat.pair idx1 n))
    (emptyDiffDec P₁ hDiff1 (Nat.pair idx1 n))
  let splitIdx := selectFn b2 (hSplitY.posIdx idx1 idx0 n) (hSplitY.negIdx idx1 idx0 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 splitIdx) (selectFn newJunk 0 directIdx) newJunk

end YSubStep

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace ySubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem idx0_eq {s n b2 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) = 0) :
    stateIdx0 (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn b2 (hSplitY.posIdx (stateIdx1 s) (stateIdx0 s) n)
        (hSplitY.negIdx (stateIdx1 s) (stateIdx0 s) n) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx0_packState2, h,
    selectFn_zero]

end AtomPairCorrect

end ySubStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace ySubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem idx1_eq {s n b2 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
      (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) = 0) :
    stateIdx1 (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn b2 (P₁.inter (stateIdx1 s) n) (hDiff1.diffIdx (stateIdx1 s) n) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx1_packState2, h,
    selectFn_zero]

end AtomPairCorrect

end ySubStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace ySubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem junk_eq (s n b2 : ℕ) :
    stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
        (emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateJunk_packState2]

end AtomPairCorrect

end ySubStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace ySubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect2

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

include hD₁pos hD₁nomin hD₁diff hySplit in
/-- **The `Y`-sub-step matches `yStepG` exactly**, symmetric to `xSubStep.correct`. -/
theorem correct {s n : ℕ} {A : Set α} {B : Set β}
    (hA : P₀.X (stateIdx0 s) = A) (hB : P₁.X (stateIdx1 s) = B)
    (hBA : B = ∅ ↔ A = ∅) (hAmem : A = ∅ ∨ D₀.mem A) (b : Bool)
    (hnonjunk : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s))) = 0) :
    P₀.X (stateIdx0 (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (yStepG splitY A B (P₁.X n) b).1 ∧
    P₁.X (stateIdx1 (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (yStepG splitY A B (P₁.X n) b).2 := by
  have hspec2 := hySplit hBA hAmem (P₁.X n)
  subst hA; subst hB
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, ite_true] at hnonjunk ⊢
    rw [ySubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₁.X (stateIdx1 s) ∩ P₁.X n ≠ ∅ :=
      (emptyInterDec.eq_one_iff P₁ hD₁pos hD₁nomin (stateIdx1 s) n).not.mp (by omega)
    have hne : (splitY (P₁.X (stateIdx1 s)) (P₀.X (stateIdx0 s)) (P₁.X n)).1 ≠ ∅ :=
      hspec2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [ySubStep.idx0_eq (h := hnonjunk), selectFn_one]
      exact (hSplitY.posIdx_spec (stateIdx1 s) (stateIdx0 s) n hne).symm
    · rw [ySubStep.idx1_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₁ hemp
  · simp only [yStepG, xyStep, Prod.swap, hb, Bool.false_eq_true, ite_false] at hnonjunk ⊢
    rw [ySubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₁.X (stateIdx1 s) \ P₁.X n ≠ ∅ :=
      (emptyDiffDec.eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin (stateIdx1 s) n).not.mp (by omega)
    have hne : (splitY (P₁.X (stateIdx1 s)) (P₀.X (stateIdx0 s)) (P₁.X n)).2 ≠ ∅ :=
      hspec2.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [ySubStep.idx0_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitY.negIdx_spec (stateIdx1 s) (stateIdx0 s) n hne).symm
    · rw [ySubStep.idx1_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff1 hemp

end AtomPairCorrect2

end ySubStep
end DomainTheory.NeighbourhoodSystems
