module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.exists_deltaPair_ne_of_lt_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.junk_eq_zero_of_selectFn_eq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.mem_XPseqCode_iff_unconditional
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_subset_atomPairIdx1

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCodeIFormula

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
  (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

/-- **8.12(d)(5)(b)(i): the `X`-side I-formula for `XPseqCode`**, the code-level, bounded-existential
analogue of `Exercise812c.lean`'s `xStep_snd_eq_inter_XPseq`. See the section docstring above for why
the `⊇` direction needs no δ'-agreement case split, unlike the classical proof. -/
theorem xPseqAtomIdx_eq_inter_XPseqCode {n k : ℕ} (hk : k < 4 ^ n)
    (hjunk : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0) :
    P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨xPseqAtomIdx_subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk hz, ?_⟩
    exact (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n z).mpr
      ⟨k, hk, hjunk, hz⟩
  · rintro z ⟨hzB, hzXP⟩
    obtain ⟨k', hk', hjunk', hz'⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX
      hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
      hD₁mne hUnion1 n z).mp hzXP
    by_cases hkk' : k' = k
    · rwa [hkk'] at hz'
    · exfalso
      have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 := by
        have h := hjunk
        rw [xPseqAtomJunk_eq] at h
        exact junk_eq_zero_of_selectFn_eq_zero h
      have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 := by
        have h := hjunk'
        rw [xPseqAtomJunk_eq] at h
        exact junk_eq_zero_of_selectFn_eq_zero h
      obtain ⟨i, hi, hne⟩ := exists_deltaPair_ne_of_lt_of_ne hk' hk hkk'
      have hdisj := (atomPairCodeState_disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨i, hi, hne⟩).2
      have hz'' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') :=
        xPseqAtomIdx_subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk' hz'
      exact absurd (Set.mem_inter hz'' hzB) (by rw [hdisj]; simp)

end XPseqCodeIFormula

end DomainTheory.NeighbourhoodSystems
