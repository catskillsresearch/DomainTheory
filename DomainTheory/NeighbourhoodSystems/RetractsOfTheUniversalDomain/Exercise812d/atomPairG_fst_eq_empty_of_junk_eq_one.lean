/-ai
If the junk flag of a bit-source at depth n equals 1, then the first component of the generalized atom pair along that bit-source's history is empty.

The argument is induction on n. At depth zero the flag is 0, a contradiction. At a successor, a flag that was already positive at the previous depth equals 1, and the first component only shrinks, so the inductive hypothesis applies. If the junk is fresh, the previous state is correct and the step unfolds into a selection of the X emptiness check and the Y emptiness check. If the X check does not fire, the X sub-step is non-junk and correct, the Y check says the second component at the next depth is empty, and the invariant transfers emptiness to the first component. If the X check fires, the direct-refine piece is empty, and the next first component sits inside that piece.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateBase2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xwB1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xwS
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairBase
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.pcN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.pcT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_le_one

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCorrect5

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(c)(v): the converse-biconditional.** Once a bit-source `i`'s recorded state at
depth `n` is genuinely junk, the classical `atomPairG`-component at that depth is already `∅` (the
`D₀`-side; contrapositive-equivalent to `(atomPairG ... n).1 ≠ ∅ → atomPairJunk n i = 0`). Proved
by induction on `n`: a junk state at depth `n + 1` either (i) was *already* junk at depth `n` (the
induction hypothesis, then propagated forward via `atomPairG_fst_subset`), or (ii) is *freshly*
created at this very step by exactly one of the two half-steps' direct-refine checks tripping —
the `X`-sub-step's check trips the `D₀`-side directly (mirrored onto `atomPairG`'s own `A1`, then
propagated to `A2` via `yStepG_fst_subset`), or the `Y`-sub-step's check trips the `D₁`-side
directly (`B2`, transferred to the `D₀`-side via `atomPairG_invariant`'s dichotomy at `n + 1`). -/
theorem atomPairG_fst_eq_empty_of_junk_eq_one (i : ℕ) : ∀ n,
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 →
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 = ∅ := by
  intro n
  induction n with
  | zero =>
    intro h
    exfalso
    have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i = 0 := by
      simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
    omega
  | succ n ih =>
    intro hjunk1
    rcases Nat.eq_zero_or_pos (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      with hn0 | hnpos
    · -- freshly junk at this step: chase the per-step algebra
      obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hn0
      unfold atomPairJunk at hjunk1 hn0
      unfold atomPairIdx0 at hidx0
      unfold atomPairIdx1 at hidx1
      rw [atomPairCodeState_succ] at hjunk1
      unfold atomPairStep pcN pcT xwB1 xwS at hjunk1
      simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk1 hidx0 hidx1
      set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair i n)
        with hTdef
      have hrem : stateRemC T = i / 4 ^ n :=
        stateRemC_atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
      have hb1 : stateRemC T % 2 = if (deltaPair i n).1 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n) with h0 | h1
        · have hδ : (deltaPair i n).1 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).1 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      have hb2 : stateRemC T / 2 % 2 = if (deltaPair i n).2 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n / 2) with h0 | h1
        · have hδ : (deltaPair i n).2 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).2 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      rw [hb1, hb2] at hjunk1
      rw [ySubStep_junk_eq] at hjunk1
      rw [xSubStep_junk_eq, hn0, selectFn_zero] at hjunk1
      -- `hjunk1 : selectFn xcheck 1 ycheck = 1`, `xcheck`/`ycheck` the two direct-refine checks
      have hb1le : (if (deltaPair i n).1 then (1 : ℕ) else 0) ≤ 1 := by
        rcases Bool.eq_false_or_eq_true (deltaPair i n).1 with h | h <;> simp [h]
      have hxle : selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) ≤ 1 :=
        selectFn_le_one hb1le (emptyInterDec_le_one P₀ _) (emptyDiffDec_le_one P₀ hDiff0 _)
      rcases Nat.eq_zero_or_pos (selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n))) with hx0 | hxpos
      · -- the `X`-sub-step's check didn't trip: it's genuinely non-junk, so chase the `Y`-check
        rw [hx0, selectFn_zero] at hjunk1
        have hxnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
            (Nat.pair n (Nat.pair (if (deltaPair i n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
          rw [xSubStep_junk_eq, hn0, selectFn_zero]; exact hx0
        obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        obtain ⟨hxA1, hxB1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
          hxSplit hidx0 hidx1 ihAB ihB (deltaPair i n).1 hxnonjunk
        have hB2 : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) (n + 1)).2 = ∅ := by
          rw [atomPairG_succ_eq]
          by_cases hδ2 : (deltaPair i n).2 = true
          · simp only [hδ2, ite_true] at hjunk1
            rw [selectFn_one] at hjunk1
            have hBe := (emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hjunk1
            rw [hxB1] at hBe
            simp only [yStepG, xyStep, Prod.swap, hδ2, ite_true]
            exact hBe
          · simp only [hδ2, Bool.false_eq_true, ite_false] at hjunk1
            rw [selectFn_zero] at hjunk1
            have hBe := (emptyDiffDec_eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin _ _).mp hjunk1
            rw [hxB1] at hBe
            simp only [yStepG, xyStep, Prod.swap, hδ2, Bool.false_eq_true, ite_false]
            exact hBe
        exact (atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX
          hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) (n + 1)).1.mpr hB2
      · -- the `X`-sub-step's check tripped: the direct-refine component is already `∅`
        have hx1 : selectFn (if (deltaPair i n).1 then 1 else 0)
            (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
            (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) = 1 := by omega
        have hA1eq : (xStepG splitX
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n)
            (deltaPair i n).1).1 = ∅ := by
          by_cases hδ1 : (deltaPair i n).1 = true
          · simp only [xStepG, xyStep, hδ1, ite_true] at hx1 ⊢
            rw [selectFn_one] at hx1
            have hAe := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
          · simp only [xStepG, xyStep, hδ1, Bool.false_eq_true, ite_false] at hx1 ⊢
            rw [selectFn_zero] at hx1
            have hAe := (emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        rw [atomPairG_succ_eq]
        exact Set.subset_eq_empty
          (yStepG_fst_subset hySplit hspecAB hspecAmem (P₁.X n) (deltaPair i n).2) hA1eq
    · -- already junk at depth `n`: propagate forward
      have hn1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
        have := atomPairJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
        omega
      exact Set.subset_eq_empty (atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n) (ih hn1)

end AtomPairCorrect5

end DomainTheory.NeighbourhoodSystems
