module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.exists_atomPairG_deltaPair_inter_Xn_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_eq_zero_of_ne_empty

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCodeUnconditional

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **8.12(d)(4)(c)(vi), step 1: the unconditional "found" existential.** Combines
`exists_atomPairG_deltaPair_inter_Xn_ne_empty` (some bit-source `i < 4ⁿ` whose depth-`n` `D₀`-side
classical piece meets `P₀.X n`) with `atomPairJunk_eq_zero_of_ne_empty` (a non-empty classical
piece forces its recorded state non-junk) and `atomPairCodeState_correct`'s forward half (rewriting
the now-known-non-junk classical piece as the code-indexed `P₀.X (atomPairIdx0 ...)`) to land the
non-trivial intersection at the *code* level, `P₀.X (atomPairIdx0 ... n i) ∩ P₀.X n ≠ ∅`. Reading
this off `emptyInterDec`'s converse (`emptyInterDec_eq_one_iff`, contrapositive via
`emptyInterDec_le_one`) gives exactly `emptyInterDec P₀ (atomPairIdx0 ... n i, n) = 0`, which is
`xPseqAtomJunk_eq`'s defining condition once `atomPairJunk n i = 0` collapses the `selectFn`. -/
theorem xPseqAtomJunk_exists_zero (n : ℕ) :
    ∃ i < 4 ^ n, xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  obtain ⟨i, hi, hne⟩ := exists_atomPairG_deltaPair_inter_Xn_ne_empty P₀ P₁ splitX splitY
    hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne hD₀nomin n
  have hAne : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ≠ ∅ := fun hA =>
    hne (Set.subset_eq_empty Set.inter_subset_left hA)
  have hjunk0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hAne
  obtain ⟨hidx0, -⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n hjunk0
  have hne' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) ∩
      P₀.X n ≠ ∅ := by rw [hidx0]; exact hne
  refine ⟨i, hi, ?_⟩
  rw [xPseqAtomJunk_eq, hjunk0, selectFn_zero]
  by_contra hcon
  have hle := emptyInterDec_le_one P₀ (Nat.pair
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)
  have h1 : emptyInterDec P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n) = 1 := by omega
  exact hne' ((emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1)

end XPseqCodeUnconditional

end DomainTheory.NeighbourhoodSystems
