module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableUnion

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

noncomputable def xPseqAtomState (n i : ℕ) : ℕ :=
  xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair 1
    (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))))

end XPseqCode

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

noncomputable def xPseqAtomJunk (n i : ℕ) : ℕ :=
  stateJunk (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)

end XPseqCode

namespace xPseqAtomJunk
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem eq (n i : ℕ) :
    xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i =
      selectFn (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) 1
        (emptyInterDec P₀ (Nat.pair
          (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)) := by
  unfold xPseqAtomJunk xPseqAtomState
  rw [xSubStep.junk_eq, stateIdx0_packState2, stateJunk_packState2, selectFn_one]

theorem le_one (n i : ℕ) :
    xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i ≤ 1 := by
  rw [xPseqAtomJunk.eq]
  exact selectFn.le_one (atomPairJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n)
    (le_refl 1) (emptyInterDec.le_one P₀ _)

theorem zero_or_one (n i : ℕ) :
    xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 ∨
      xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
  have := xPseqAtomJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
  omega

end XPseqCode

end xPseqAtomJunk

end DomainTheory.NeighbourhoodSystems
