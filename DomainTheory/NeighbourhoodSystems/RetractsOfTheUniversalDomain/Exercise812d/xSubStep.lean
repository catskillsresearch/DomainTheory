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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

/-- **The `X`-sub-step.** Refines `D₀`'s side (`idx0`) directly against `P₀.X n` (intersect if
`b1 = 1`, diff if `b1 = 0`, via `P₀.inter`/`hDiff0.diffIdx`), and `D₁`'s side (`idx1`) via the
matching branch of the split `hSplitX` — freezing both at the junk sentinel `0` the moment either
the incoming state was already junk, or this step's direct refinement is found empty. -/
noncomputable def xSubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b1 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b1 (P₀.inter idx0 n) (hDiff0.diffIdx idx0 n)
  let directEmpty := selectFn b1 (emptyInterDec P₀ (Nat.pair idx0 n))
    (emptyDiffDec P₀ hDiff0 (Nat.pair idx0 n))
  let splitIdx := selectFn b1 (hSplitX.posIdx idx0 idx1 n) (hSplitX.negIdx idx0 idx1 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 directIdx) (selectFn newJunk 0 splitIdx) newJunk

end XSubStep

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xSubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem idx0_eq {s n b1 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) = 0) :
    stateIdx0 (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn b1 (P₀.inter (stateIdx0 s) n) (hDiff0.diffIdx (stateIdx0 s) n) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx0_packState2, h,
    selectFn_zero]

end AtomPairCorrect

end xSubStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xSubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem idx1_eq {s n b1 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) = 0) :
    stateIdx1 (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn b1 (hSplitX.posIdx (stateIdx0 s) (stateIdx1 s) n)
        (hSplitX.negIdx (stateIdx0 s) (stateIdx1 s) n) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx1_packState2, h,
    selectFn_zero]

end AtomPairCorrect

end xSubStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xSubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem junk_eq (s n b1 : ℕ) :
    stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
        (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateJunk_packState2]

end AtomPairCorrect

end xSubStep
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace xSubStep

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

include hD₀pos hD₀nomin hD₀diff hxSplit in
/-- **The `X`-sub-step matches `xStepG` exactly**, given the previous state's indices already match
`A`/`B` and the sub-step's output is non-junk. **No longer fully unconditional in `A`/`B`** (2026-
07-06, repairing 8.12(g)): now that `posIdx_spec`/`negIdx_spec` are conditional on non-emptiness,
deriving the split side needs `SplitSpec'`'s "empty iff empty" conjunct, which itself needs the
`atomPairG.invariant`-style precondition on `A`/`B` (`hAB`/`hBmem`) to fire. At every call site
these come straight from `atomPairG.invariant`/`xStepG.spec`. -/
theorem correct {s n : ℕ} {A : Set α} {B : Set β}
    (hA : P₀.X (stateIdx0 s) = A) (hB : P₁.X (stateIdx1 s) = B)
    (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (b : Bool)
    (hnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s))) = 0) :
    P₀.X (stateIdx0 (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (xStepG splitX A B (P₀.X n) b).1 ∧
    P₁.X (stateIdx1 (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (xStepG splitX A B (P₀.X n) b).2 := by
  have hspec1 := hxSplit hAB hBmem (P₀.X n)
  subst hA; subst hB
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, ite_true] at hnonjunk ⊢
    rw [xSubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₀.X (stateIdx0 s) ∩ P₀.X n ≠ ∅ :=
      (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).1 ≠ ∅ :=
      hspec1.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep.idx0_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₀ hemp
    · rw [xSubStep.idx1_eq (h := hnonjunk), selectFn_one]
      exact (hSplitX.posIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm
  · simp only [xStepG, xyStep, hb, Bool.false_eq_true, ite_false] at hnonjunk ⊢
    rw [xSubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₀.X (stateIdx0 s) \ P₀.X n ≠ ∅ :=
      (emptyDiffDec.eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).2 ≠ ∅ :=
      hspec1.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep.idx0_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff0 hemp
    · rw [xSubStep.idx1_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitX.negIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm

end AtomPairCorrect2

end xSubStep
end DomainTheory.NeighbourhoodSystems
