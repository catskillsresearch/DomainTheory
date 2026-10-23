module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **The depth-`n` shared junk flag**, for bit-source `k` (`1` iff both sides are already `∅`). -/
noncomputable def atomPairJunk (n k : ℕ) : ℕ :=
  stateJunk (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

end AtomPairCode

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairJunk

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

/-- **The depth-`0` state is never junk**, for any bit-source `k`: `atomPairCodeState`'s own base
clause (`stateBase2`) hardcodes junk `0`, regardless of `k`. -/
theorem zero (k : ℕ) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 k = 0 := by
  unfold atomPairJunk
  simp [atomPairCodeState, atomPairBase, stateBase2]

end XYPseqCodeZero

end atomPairJunk
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairJunk

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

/-- **`atomPairJunk` propagates**: once a bit-source's depth-`(n+1)` state is non-junk, its
depth-`n` state already was (the contrapositive of "junk is frozen forever", a one-step algebraic
fact needing no induction: `xSubStep`/`ySubStep` both force their *output* junk flag to `1`
whenever their *input* junk flag already was, via `selectFn junk 1 _`). -/
theorem eq_zero_of_succ {k n : ℕ}
    (h : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 0) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 := by
  unfold atomPairJunk at h ⊢
  rw [atomPairCodeState.succ] at h
  unfold atomPairStep pcN pcT xwB1 xwS at h
  simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at h
  rw [ySubStep.junk_eq] at h
  have h1 := junk_eq_zero_of_selectFn_eq_zero h
  rw [xSubStep.junk_eq] at h1
  exact junk_eq_zero_of_selectFn_eq_zero h1

end AtomPairCorrect

end atomPairJunk
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace atomPairJunk

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

/-- **`atomPairJunk` is always `0` or `1`** (never any other natural number), by induction through
the nested `selectFn`s: the base case is the literal `0` of `stateBase2`, and each step is a chain
of `selectFn.le_one` applications — the outer flag bounded by the outer induction hypothesis, the
inner emptiness deciders bounded by `emptyInterDec.le_one`/`emptyDiffDec.le_one`. -/
theorem le_one (k n : ℕ) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k ≤ 1 := by
  induction n with
  | zero => simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
  | succ n ih =>
    unfold atomPairJunk at ih ⊢
    rw [atomPairCodeState.succ]
    unfold atomPairStep pcN pcT xwB1 xwS
    simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC]
    set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k n)
    rw [ySubStep.junk_eq, xSubStep.junk_eq]
    have hb1 : stateRemC T % 2 ≤ 1 := Nat.le_of_lt_succ (by omega)
    have hb2 : stateRemC T / 2 % 2 ≤ 1 := Nat.le_of_lt_succ (by omega)
    exact selectFn.le_one
      (selectFn.le_one ih (le_refl 1)
        (selectFn.le_one hb1 (emptyInterDec.le_one P₀ _) (emptyDiffDec.le_one P₀ hDiff0 _)))
      (le_refl 1)
      (selectFn.le_one hb2 (emptyInterDec.le_one P₁ _) (emptyDiffDec.le_one P₁ hDiff1 _))

end AtomPairCorrect2

end atomPairJunk
end DomainTheory.NeighbourhoodSystems
