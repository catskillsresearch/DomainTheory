/-ai
For an arbitrary sign history and a depth n, the second component of the positive generalized X-step on the depth-n generated pair equals the intersection of that pair's second component with the basic neighbourhood of the X-sequence code of n.

Encode the history through depth n as a bit-source below 4 to the power n. The history and the bit-source agree below n, so the generated pairs agree. If the second component is empty, the split specification makes the positive branch empty, and both sides of the goal are empty. Otherwise the atom-pair at that bit-source is not junk. If the half-step atom is not junk, the bounded intersection formula, the closed form of its index, and a vanishing selection give a nonempty intersection of the first component with the basic neighbourhood of n, hence a nonempty positive branch; the positive-index specification identifies the half-step neighbourhood with that branch, and the bounded formula rewrites it as the required intersection. If the half-step atom is junk, its flag is 1 because the flag is at most 1, and the junk formula makes the first-component intersection empty, so the positive branch is empty. The second component is disjoint from the sequence neighbourhood, because a common point would lie in another non-junk half-step atom, a distinguishing digit would make the two atom-pair neighbourhoods disjoint, and the point would lie in both. Both sides are therefore empty.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.exists_deltaPair_ne_of_lt_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.encodeDeltaPair_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair_encodeDeltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.junk_eq_zero_of_selectFn_eq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.selectFn_one_eq_zero_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_eq_zero_of_snd_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.mem_XPseqCode_iff_unconditional
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_subset_atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_eq_inter_XPseqCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

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

/-- **The `X`-side I-formula, generalized to an arbitrary `δ`** (not just a bounded bit-source `k <
4 ^ n`): the `X`-sub-step's own `"+"`/`true` branch, run on `atomPairG`'s depth-`n` component for
*any* history `δ`, is exactly the intersection of that component's `D₁`-side with `XPseqCode n`.
Bridges `(b)(i)`'s bounded-existential `xPseqAtomIdx_eq_inter_XPseqCode` up to the fully general
statement `Exercise812c.lean`'s own `xStep_snd_eq_inter_XPseq` makes, via `encodeDeltaPair δ n` as
the bounded representative: if the represented component is already `∅`, both sides are `∅`
directly from `SplitSpec'`; otherwise `(d)(4)(c)(v)`'s `atomPairJunk_eq_zero_of_snd_ne_empty` gives
a non-junk bit-source to feed `(b)(i)`'s headline, *unless* the fresh half-step atom is itself junk
— handled by the "junk-mismatch" trick documented at the section level. -/
theorem xStepG_snd_eq_inter_XPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) :
    (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) true).2 =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 ∩
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) := by
  simp only [xStepG, xyStep, ite_true]
  set k := encodeDeltaPair δ n with hkdef
  have hklt : k < 4 ^ n := encodeDeltaPair_lt δ n
  have hagree : ∀ i < n, δ i = deltaPair k i := fun i hi =>
    (deltaPair_encodeDeltaPair δ n i hi).symm
  have hcongr : atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n =
      atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n :=
    atomPairG_congr D₀ D₁ splitY splitX P₀.X P₁.X hagree
  rw [hcongr]
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 with hBdef
  obtain ⟨hAB, -, hBmem⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
  rw [← hAdef] at hAB
  rw [← hBdef] at hAB hBmem
  by_cases hB : B = ∅
  · have hspec := hxSplit hAB (Or.inl hB) (P₀.X n)
    have hunion := hspec.2.2.2.2.1
    have h1empty : (splitX A B (P₀.X n)).1 = ∅ :=
      Set.subset_eq_empty Set.subset_union_left (hunion.trans hB)
    rw [h1empty, hB]; simp
  · have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 :=
      atomPairJunk_eq_zero_of_snd_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hB
    have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hAjunk
    by_cases hxj : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0
    · have hIF := xPseqAtomIdx_eq_inter_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 hklt
        hxj
      have hidxeq := xPseqAtomIdx_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxj
      have hraw' := hxj
      rw [xPseqAtomJunk_eq] at hraw'
      obtain ⟨-, hempty0'⟩ := selectFn_one_eq_zero_iff.mp hraw'
      have hAeq : A = P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) :=
        hAdef.trans hcs.1.symm
      have hempty'' : A ∩ P₀.X n ≠ ∅ := by
        rw [hAeq]
        exact (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).not.mp (by omega)
      have hne : (splitX A B (P₀.X n)).1 ≠ ∅ := by
        have hspecAB := hxSplit hAB hBmem (P₀.X n)
        exact hspecAB.2.2.1.not.mp hempty''
      have hposspec := hSplitX.posIdx_spec
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) n
        (by rw [hcs.1, hcs.2]; exact hne)
      rw [hcs.1, hcs.2] at hposspec
      have hgoal2 : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
          (splitX A B (P₀.X n)).1 := by rw [hidxeq]; exact hposspec.symm
      rw [← hgoal2, hIF, hcs.2]
    · have hxj1 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 1 := by
        have := xPseqAtomJunk_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
        omega
      have h2empty : (splitX A B (P₀.X n)).1 = ∅ := by
        have h := hxj1
        rw [xPseqAtomJunk_eq, hAjunk, selectFn_zero] at h
        have hempty := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h
        rw [hcs.1] at hempty
        have hspec := hxSplit hAB hBmem (P₀.X n)
        exact hspec.2.2.1.mp hempty
      have hdisjXP : B ∩
          P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzB, hzXP⟩
        obtain ⟨k', hk'lt, hjunk', hz'⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1
          splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
          hySplit hD₀mne hD₁mne hUnion1 n z).mp hzXP
        have hkk' : k' ≠ k := by rintro rfl; omega
        have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 := by
          have h := hjunk'
          rw [xPseqAtomJunk_eq] at h
          exact junk_eq_zero_of_selectFn_eq_zero h
        have hz'' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') :=
          xPseqAtomIdx_subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
            hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk' hz'
        have hzB' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) :=
          hcs.2 ▸ hzB
        obtain ⟨i, hi, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hklt hk'lt hkk'.symm
        have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
          (n := n) (k := k) (k' := k') hAjunk hAjunk' ⟨i, hi, hne⟩).2
        exact absurd (Set.mem_inter hzB' hz'') (by rw [hdisj]; simp)
      rw [h2empty, hdisjXP]

end CombinedCode

end DomainTheory.NeighbourhoodSystems
