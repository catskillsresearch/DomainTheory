module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_disjoint_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.exists_deltaPair_ne_of_lt_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_eq_zero_of_yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx_subset_xStepGFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx_subset_atomPairIdx0

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCodeIFormula

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
  (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **The two-source disjointness dichotomy** feeding the I-formula's `⊇` direction: given a
witness bit-source/bit pair `(i', b')` whose atom contains `z` and a target pair `(i, b)` with `z`
already known to lie in the *classical* `xStepG`-level piece at `(i, b)`, either `(i', b') = (i, b)`
(so the witness atom already *is* the target atom) or the two atoms are disjoint — from either
`atomPairCodeState_disjoint` (if `i' ≠ i`, transported up through
`yPseqAtomIdx_subset_atomPairIdx0`) or `xStepG_disjoint_of_ne` (if `i' = i` but `b' ≠ b`, transported
up through `yPseqAtomIdx_subset_xStepGFst`) — a contradiction with the disjointness in either case. -/
theorem yPseqAtomIdx_eq_of_dichotomy {n i i' : ℕ} {z : α} (b b' : Bool)
    (hi : i < 4 ^ n) (hi' : i' < 4 ^ n)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0)
    (hjunk' : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i'
      (if b' then 1 else 0) = 0)
    (hzA1 : z ∈ (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1)
    (hz' : z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i'
      (if b' then 1 else 0))) :
    z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0)) := by
  by_cases hii' : i' = i
  · by_cases hbb' : b' = b
    · rw [hii', hbb'] at hz'
      exact hz'
    · exfalso
      rw [hii'] at hjunk' hz'
      have hz'' : z ∈ (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b').1 :=
        yPseqAtomIdx_subset_xStepGFst P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b' hjunk' hz'
      obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
      have hdisj := (xStepG_disjoint_of_ne hxSplit ihAB ihB (P₀.X n) (b := b) (b' := b')
        (Ne.symm hbb')).1
      exact absurd (Set.mem_inter hzA1 hz'') (by rw [hdisj]; simp)
  · exfalso
    have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
      atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b
        hjunk
    have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i' = 0 :=
      atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b'
        hjunk'
    obtain ⟨j, hj, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hi' hi hii'
    have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne (n := n)
      (k := i') (k' := i) hAjunk' hAjunk ⟨j, hj, hne⟩).1
    have hzA : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) := by
      have hAeq := (atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hAjunk).1
      rw [hAeq]
      exact (xStepG_fst_subset splitX _ _ (P₀.X n) b) hzA1
    have hzA' : z ∈ P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i') :=
      yPseqAtomIdx_subset_atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne b' hjunk' hz'
    exact absurd (Set.mem_inter hzA' hzA) (by rw [hdisj]; simp)

end YPseqCodeIFormula

end DomainTheory.NeighbourhoodSystems
