module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_6
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace yStepG

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

/-- **The `Y`-side I-formula, generalized to an arbitrary `δ`** (not just a bounded bit-source
`k < 4 ^ n`) **and a free `bx : Bool`** (not just the bit `δ n).1` itself, matching
`Exercise812c.lean`'s own `yStep.fst_eq_inter_YPseq`): the `Y`-sub-step's `"+"`/`true` branch, run
on `xStepG`'s own output at *any* bit `bx` and *any* history `δ`, is exactly the intersection of
that output's `D₀`-side with `YPseqCode n`. Same overall strategy as
`xStepG.snd_eq_inter_XPseqCode`: encode `δ`'s depth-`n` prefix as `k := encodeDeltaPair δ n`, handle
`A1 = ∅` directly via `SplitSpec'`, and otherwise split on `yPseqAtomJunk n k (if bx then 1 else 0)`
— zero feeds `(b)(ii)`'s headline (after bridging its `yPseqAtomIdx` back to the `yStepG`-level via
`xSubStep.correct`/`ySubStep.correct`, mirroring `yPseqAtomIdx.subset_xStepGFst`'s own internal
`hgoaleq`); one is "fresh junk" at *this* extra half-step, handled by first showing the `X`-sub-step
itself must still be non-junk (else `A1 = ∅`, contradicting the case hypothesis), so the freshness
must come from the `Y`-sub-step's own direct-refine check, giving `B1 ∩ Yn = ∅` and hence the goal's
`true`-branch output is `∅` directly; the `∩ YPseqCode` side is then `∅` via the same
"junk-mismatch" disjointness trick as the `X`-side, now with an extra case split on the witness's
own `bx'`-bit (`xStepG.disjoint_of_ne` when the bit differs at the same `k`, else
`atomPairCodeState.disjoint` as before). -/
theorem fst_eq_inter_YPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (bx : Bool) :
    (yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) bx).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) bx).2
        (P₁.X n) true).1 =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) bx).1 ∩
        P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) := by
  set k := encodeDeltaPair δ n with hkdef
  have hklt : k < 4 ^ n := encodeDeltaPair_lt δ n
  have hagree : ∀ i < n, δ i = deltaPair k i := fun i hi =>
    (deltaPair.encodeDeltaPair δ n i hi).symm
  have hcongr : atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n =
      atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n :=
    atomPairG.congr D₀ D₁ splitY splitX P₀.X P₁.X hagree
  rw [hcongr]
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 with hBdef
  set A1 := (xStepG splitX A B (P₀.X n) bx).1 with hA1def
  set B1 := (xStepG splitX A B (P₀.X n) bx).2 with hB1def
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
    rw [hA1def, hB1def]
    by_cases hbx : bx = true
    · simp only [xStepG, xyStep, hbx, ite_true]; exact hspec1.2.2.1
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]; exact hspec1.2.2.2.1
  have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
    rw [hA1def]
    by_cases hbx : bx = true
    · simp only [xStepG, xyStep, hbx, ite_true]; exact inter.mem_or_empty hD₀pos ihA (P₀.mem_X n)
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]
      exact diff.mem_or_empty hD₀diff ihA (P₀.mem_X n)
  by_cases hA1 : A1 = ∅
  · have hB1e : B1 = ∅ := hA1B1.mp hA1
    have hspec2 := hySplit hA1B1.symm (Or.inl hA1) (P₁.X n)
    have hunion2 := hspec2.2.2.2.2.1
    have h1empty : (yStepG splitY A1 B1 (P₁.X n) true).1 = ∅ := by
      show (splitY B1 A1 (P₁.X n)).1 = ∅
      exact Set.subset_eq_empty Set.subset_union_left (hunion2.trans hA1)
    rw [h1empty, hA1]; simp
  · have hAne : A ≠ ∅ := by
      intro h
      apply hA1
      rw [hA1def]
      exact Set.subset_eq_empty (xStepG.fst_subset splitX A B (P₀.X n) bx) h
    have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 :=
      atomPairJunk.eq_zero_of_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne (hAdef ▸ hAne)
    have hcs := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hAjunk
    set s0 := packState2
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) with hs0def
    set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if bx then 1 else 0) s0)) with hs1def
    have hidx0' : P₀.X (stateIdx0 s0) = A := by rw [hs0def, stateIdx0_packState2]; exact hcs.1
    have hidx1' : P₁.X (stateIdx1 s0) = B := by rw [hs0def, stateIdx1_packState2]; exact hcs.2
    by_cases hyj : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
        (if bx then 1 else 0) = 0
    · have hxnonjunk : stateJunk s1 = 0 := by
        have h' := hyj
        unfold yPseqAtomJunk yPseqAtomState at h'
        rw [← hs0def, ← hs1def] at h'
        rw [ySubStep.junk_eq, selectFn_one] at h'
        exact junk_eq_zero_of_selectFn_eq_zero h'
      obtain ⟨hxc0, hxc1⟩ := xSubStep.correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
        hxSplit hidx0' hidx1' ihAB ihB bx hxnonjunk
      rw [← hs1def] at hxc0 hxc1
      rw [← hA1def] at hxc0
      rw [← hB1def] at hxc1
      have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 0 := by
        have h' := hyj
        unfold yPseqAtomJunk yPseqAtomState at h'
        rwa [← hs0def, ← hs1def] at h'
      obtain ⟨hyc0, -⟩ := ySubStep.correct P₀ P₁ hDiff1 splitY hSplitY hD₁pos hD₁diff hD₁nomin
        hySplit hxc0 hxc1 hA1B1.symm hA1mem true h
      have hgoaleq : P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
          (if bx then 1 else 0)) = (yStepG splitY A1 B1 (P₁.X n) true).1 := by
        show P₀.X (stateIdx0 (yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
          (if bx then 1 else 0))) = _
        unfold yPseqAtomState
        rw [← hs0def, ← hs1def]
        exact hyc0
      have hIF := yPseqAtomIdx.eq_inter_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hklt
        bx hyj
      rw [← hA1def] at hIF
      rw [← hgoaleq, hIF]
    · have hyj1 : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
          (if bx then 1 else 0) = 1 := by
        have := yPseqAtomJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          (bx := if bx then 1 else 0) (by cases bx <;> simp) n k
        omega
      have hs1junk_eq : stateJunk s1 = selectFn (if bx then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 s0) n))
          (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s0) n)) := by
        rw [hs1def, xSubStep.junk_eq, hs0def, stateJunk_packState2, hAjunk, selectFn_zero]
      have hs1le : stateJunk s1 ≤ 1 := by
        rw [hs1junk_eq]
        exact selectFn.le_one (by cases bx <;> simp) (emptyInterDec.le_one P₀ _)
          (emptyDiffDec.le_one P₀ hDiff0 _)
      have hxnonjunk : stateJunk s1 = 0 := by
        by_contra hne
        have h3 : selectFn (if bx then 1 else 0) (emptyInterDec P₀ (Nat.pair (stateIdx0 s0) n))
            (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s0) n)) = 1 := by
          rw [← hs1junk_eq]; omega
        have hA1e : A1 = ∅ := by
          rw [hA1def]
          by_cases hbx : bx = true
          · simp only [xStepG, xyStep, hbx, ite_true]
            simp only [hbx, ite_true, selectFn_one] at h3
            rw [← hidx0']
            exact (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h3
          · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]
            simp only [hbx, Bool.false_eq_true, ite_false, selectFn_zero] at h3
            rw [← hidx0']
            exact (emptyDiffDec.eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp h3
        exact hA1 hA1e
      have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 1 := by
        have h' := hyj1
        unfold yPseqAtomJunk yPseqAtomState at h'
        rwa [← hs0def, ← hs1def] at h'
      have hyInter : emptyInterDec P₁ (Nat.pair (stateIdx1 s1) n) = 1 := by
        have h2 := h
        rw [ySubStep.junk_eq, hxnonjunk, selectFn_zero, selectFn_one] at h2
        exact h2
      obtain ⟨hxc0, hxc1⟩ := xSubStep.correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
        hxSplit hidx0' hidx1' ihAB ihB bx hxnonjunk
      rw [← hs1def] at hxc0 hxc1
      rw [← hA1def] at hxc0
      rw [← hB1def] at hxc1
      have hB1Yempty : B1 ∩ (P₁.X n) = ∅ := by
        rw [← hxc1]
        exact (emptyInterDec.eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hyInter
      have hspec2 := hySplit hA1B1.symm hA1mem (P₁.X n)
      have h1empty : (yStepG splitY A1 B1 (P₁.X n) true).1 = ∅ := by
        show (splitY B1 A1 (P₁.X n)).1 = ∅
        exact hspec2.2.2.1.mp hB1Yempty
      have hdisjYP : A1 ∩ P₀.X
          (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzA1, hzYP⟩
        obtain (⟨k', hk'lt, hjunk', hz'⟩ | ⟨k', hk'lt, hjunk', hz'⟩) :=
          (mem_YPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
            hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 n z).mp
            hzYP
        · rcases eq_or_ne k' k with hkk' | hkk'
          · exfalso
            subst hkk'
            have hbxc : bx ≠ false := by
              intro hbxeq
              have hzero : (if bx then (1 : ℕ) else 0) = 0 := by rw [hbxeq]; simp
              rw [hzero] at hyj1
              omega
            have hz'' : z ∈ (xStepG splitX A B (P₀.X n) false).1 :=
              yPseqAtomIdx.subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne false
                hjunk' hz'
            have hdisj := (xStepG.disjoint_of_ne hxSplit ihAB ihB (P₀.X n) (b := bx) (b' := false)
              hbxc).1
            rw [← hA1def] at hdisj
            exact absurd (Set.mem_inter hzA1 hz'') (by rw [hdisj]; simp)
          · have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 :=
              atomPairJunk.eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                hSplitY false hjunk'
            obtain ⟨j, hj, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hk'lt hklt hkk'
            have hdisj := (atomPairCodeState.disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
              hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
              hD₁mne (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨j, hj, hne⟩).1
            have hzAk : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k) := by
              rw [hcs.1]
              exact (xStepG.fst_subset splitX A B (P₀.X n) bx) (hA1def ▸ hzA1)
            have hzAk' : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k') :=
              yPseqAtomIdx.subset_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne false
                hjunk' hz'
            exact absurd (Set.mem_inter hzAk' hzAk) (by rw [hdisj]; simp)
        · rcases eq_or_ne k' k with hkk' | hkk'
          · exfalso
            subst hkk'
            have hbxc : bx ≠ true := by
              intro hbxeq
              have hone : (if bx then (1 : ℕ) else 0) = 1 := by rw [hbxeq]; simp
              rw [hone] at hyj1
              omega
            have hz'' : z ∈ (xStepG splitX A B (P₀.X n) true).1 :=
              yPseqAtomIdx.subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne true
                hjunk' hz'
            have hdisj := (xStepG.disjoint_of_ne hxSplit ihAB ihB (P₀.X n) (b := bx) (b' := true)
              hbxc).1
            rw [← hA1def] at hdisj
            exact absurd (Set.mem_inter hzA1 hz'') (by rw [hdisj]; simp)
          · have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 :=
              atomPairJunk.eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
                hSplitY true hjunk'
            obtain ⟨j, hj, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hk'lt hklt hkk'
            have hdisj := (atomPairCodeState.disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
              hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
              hD₁mne (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨j, hj, hne⟩).1
            have hzAk : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k) := by
              rw [hcs.1]
              exact (xStepG.fst_subset splitX A B (P₀.X n) bx) (hA1def ▸ hzA1)
            have hzAk' : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n
                k') :=
              yPseqAtomIdx.subset_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
                hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne true
                hjunk' hz'
            exact absurd (Set.mem_inter hzAk' hzAk) (by rw [hdisj]; simp)
      rw [h1empty, hdisjYP]

end CombinedCode

end yStepG
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace yStepG

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Two-branch closed form, generalized to an arbitrary `δ`** (not just a bounded bit-source `k <
4 ^ n`): completes `yStepG.fst_eq_inter_YPseqCode`'s `true`-only fact (specialized to the `X`-side
bit `(δ n).1`, exactly as `Exercise812c.lean`'s `yStep.fst_succ_eq` fixes it) into a full
`genAtom`-shaped closed step at *either* sign of the `Y`-sub-step — the `false` branch is derived
algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = A1`/`I ∩ J = ∅`, mirroring
`xStepG.snd_succ_eq_XPseqCode` exactly (with the roles of `hySplit`/`hxSplit` swapped). -/
theorem fst_succ_eq_YPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).2
        (P₁.X n) b).1 =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1 ∩
        (if b then P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)
          else D₀.master \
            P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 with hBdef
  set A1 := (xStepG splitX A B (P₀.X n) (δ n).1).1 with hA1def
  set B1 := (xStepG splitX A B (P₀.X n) (δ n).1).2 with hB1def
  set YP := P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) with hYPdef
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
    rw [hA1def, hB1def]
    by_cases hbx : (δ n).1 = true
    · simp only [xStepG, xyStep, hbx, ite_true]; exact hspec1.2.2.1
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]; exact hspec1.2.2.2.1
  have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
    rw [hA1def]
    by_cases hbx : (δ n).1 = true
    · simp only [xStepG, xyStep, hbx, ite_true]; exact inter.mem_or_empty hD₀pos ihA (P₀.mem_X n)
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]
      exact diff.mem_or_empty hD₀diff ihA (P₀.mem_X n)
  have hspec := hySplit hA1B1.symm hA1mem (P₁.X n)
  have hJeqTrue : (yStepG splitY A1 B1 (P₁.X n) true).1 = A1 ∩ YP :=
    yStepG.fst_eq_inter_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 δ n (δ n).1
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hJeqTrue
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (yStepG splitY A1 B1 (P₁.X n) false).1 = A1 \ YP := by
      have hunion :
          (yStepG splitY A1 B1 (P₁.X n) true).1 ∪ (yStepG splitY A1 B1 (P₁.X n) false).1 = A1 := by
        simp only [yStepG, xyStep, Prod.swap]; exact hspec.2.2.2.2.1
      have hinter :
          (yStepG splitY A1 B1 (P₁.X n) true).1 ∩ (yStepG splitY A1 B1 (P₁.X n) false).1 = ∅ := by
        simp only [yStepG, xyStep, Prod.swap]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxA1 : x ∈ A1 := hunion ▸ Or.inr hxJ
        refine ⟨hxA1, fun hxYP => ?_⟩
        have hxI : x ∈ (yStepG splitY A1 B1 (P₁.X n) true).1 := hJeqTrue ▸ Set.mem_inter hxA1 hxYP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxA1, hxnYP⟩
        rw [← hunion] at hxA1
        rcases hxA1 with hxI | hxJ
        · exact absurd (hJeqTrue ▸ hxI : x ∈ A1 ∩ YP).2 hxnYP
        · exact hxJ
    rw [hJeq]
    have hsub : A1 ⊆ D₀.master := (xStepG.fst_subset splitX A B (P₀.X n) (δ n).1).trans
      (atomPairG.fst_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
        P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n)
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end CombinedCode

end yStepG
end DomainTheory.NeighbourhoodSystems
