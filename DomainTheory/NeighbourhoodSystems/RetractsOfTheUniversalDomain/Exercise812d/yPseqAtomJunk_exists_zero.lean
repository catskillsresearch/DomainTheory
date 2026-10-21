/-ai
For every depth n there exist a bit-source below 4 to the power n and a bit at most 1 such that the Y half-step atom at that bit-source and bit is not junk.

Some such bit-source has generated second component meeting the basic neighbourhood of n, so that component is nonempty and the atom-pair is not junk. The generated pair satisfies the invariant, and the two split components of the generalized X-step reunite to the second component, so one of them meets the basic neighbourhood of n. The split specification promotes a nonempty split component to a nonempty direct-refinement component. The bit lemma then makes the half-step atom at bit 1, or at bit 0, not junk, according to which branch meets the neighbourhood.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_snd_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.exists_atomPairG_deltaPair_inter_Yn_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_eq_zero_of_snd_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk_eq_zero_of_bit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCodeUnconditional

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(d)(vi), step 1: the unconditional "found" existential, doubled over `bx`.**
Combines `(d)(iv)`'s `exists_atomPairG_deltaPair_inter_Yn_ne_empty` with `xStepG_snd_union`
(`(d)(i)`) to locate a bit `bx ∈ {0, 1}` whose split piece meets `P₁.X n`, the `SplitSpec'`-level
dichotomy (`hxSplit`, applied directly rather than via the depth-crossing `atomPairG_invariant`)
to promote that to the direct-refine piece being non-empty, and
`yPseqAtomJunk_eq_zero_of_bit` to land the half-step atom's junk flag at `0`. -/
theorem yPseqAtomJunk_exists_zero (n : ℕ) :
    ∃ i < 4 ^ n, ∃ bx ≤ 1,
      yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i bx = 0 := by
  obtain ⟨i, hi, hBinter⟩ := exists_atomPairG_deltaPair_inter_Yn_ne_empty P₀ P₁ splitX splitY
    hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₁nomin n
  have hBne : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ≠ ∅ := fun hB =>
    hBinter (by rw [hB]; simp)
  have hjunk0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_snd_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hBne
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
  have hunion := xStepG_snd_union hxSplit ihAB ihB (P₀.X n)
  rw [← hunion, Set.union_inter_distrib_right] at hBinter
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hex : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) true).2 ∩
      P₁.X n ≠ ∅ ∨
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) false).2 ∩
      P₁.X n ≠ ∅ := by
    by_contra hcon
    push Not at hcon
    exact hBinter (by rw [hcon.1, hcon.2]; simp)
  rcases hex with hTinter | hFinter
  · have hTne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) true).2 ≠ ∅ :=
      fun h => hTinter (by rw [h]; simp)
    have hA1ne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) true).1 ≠ ∅ :=
      mt hspec1.2.2.1.mp hTne
    have hzero := yPseqAtomJunk_eq_zero_of_bit P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk0 true
      hA1ne hTinter
    exact ⟨i, hi, 1, le_refl 1, hzero⟩
  · have hFne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) false).2 ≠ ∅ :=
      fun h => hFinter (by rw [h]; simp)
    have hA1ne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) false).1 ≠ ∅ :=
      mt hspec1.2.2.2.1.mp hFne
    have hzero := yPseqAtomJunk_eq_zero_of_bit P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk0 false
      hA1ne hFinter
    exact ⟨i, hi, 0, Nat.zero_le 1, hzero⟩

end YPseqCodeUnconditional

end DomainTheory.NeighbourhoodSystems
