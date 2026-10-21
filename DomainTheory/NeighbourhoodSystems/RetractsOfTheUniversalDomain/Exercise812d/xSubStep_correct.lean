/-ai
If a packed state's two indices denote sets that are empty together, the second set is empty or genuine, and the X sub-step at a neighbourhood index and a bit is not junk, then the output indices denote the two components of the generalized X-step of those sets, the basic neighbourhood of the index, and the bit.

The split specification applies. If the bit is true, the junk formula and a vanishing selection make the intersection emptiness decision vanish, so the intersection and the positive branch are nonempty. The first-index formula with selection at bit 1 and the intersection-index lemma give the first component, and the second-index formula with the positive-index specification gives the second. If the bit is false, the same argument with the difference emptiness decision, the difference-index lemma, and the negative-index specification gives the two components of the negative step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_idx0_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_idx1_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn_one_eq_zero_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.interIdx_eq_of_empty_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.diffIdx_eq_of_empty_zero

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

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
`atomPairG_invariant`-style precondition on `A`/`B` (`hAB`/`hBmem`) to fire. At every call site
these come straight from `atomPairG_invariant`/`xStepG_spec`. -/
theorem xSubStep_correct {s n : ℕ} {A : Set α} {B : Set β}
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
    rw [xSubStep_junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn_one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₀.X (stateIdx0 s) ∩ P₀.X n ≠ ∅ :=
      (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).1 ≠ ∅ :=
      hspec1.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep_idx0_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₀ hemp
    · rw [xSubStep_idx1_eq (h := hnonjunk), selectFn_one]
      exact (hSplitX.posIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm
  · simp only [xStepG, xyStep, hb, Bool.false_eq_true, ite_false] at hnonjunk ⊢
    rw [xSubStep_junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn_one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₀.X (stateIdx0 s) \ P₀.X n ≠ ∅ :=
      (emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).2 ≠ ∅ :=
      hspec1.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep_idx0_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff0 hemp
    · rw [xSubStep_idx1_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitX.negIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm

end AtomPairCorrect2

end DomainTheory.NeighbourhoodSystems
