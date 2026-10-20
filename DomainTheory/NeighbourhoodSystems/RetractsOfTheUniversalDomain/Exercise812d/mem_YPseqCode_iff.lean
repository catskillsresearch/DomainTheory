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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combineFound2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combineFound2_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_found_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_found_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_mem_of_found
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin in
/-- **The closed-form membership characterization of `YPseqCode`, conditional on "found" at
`N = 4ⁿ`**: a point lies in `P₀.X (YPseqCode n)` iff it lies in some genuine (non-junk) half-step
atom `yPseqAtomIdx n i bx`, for `i < 4ⁿ` on *either* `bx`-branch. -/
theorem mem_YPseqCode_iff {n : ℕ}
    (hfound : (combineFound2 hUnion0
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))
      ).unpair.1 = 1) (z : α) :
    z ∈ P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) ↔
      (∃ i < 4 ^ n, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 0 = 0 ∧
        z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 0)) ∨
      (∃ i < 4 ^ n, yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 1 = 0 ∧
        z ∈ P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i 1)) := by
  have hle0 := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
    (Nat.zero_le 1) n (4 ^ n)
  have hle1 := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
    (le_refl 1) n (4 ^ n)
  have hmem0 := YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n)
  have hmem1 := YFoldInner_mem_of_found P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hUnion0 (le_refl 1) n (4 ^ n)
  have heq : YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n =
      (combineFound2 hUnion0
        (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
        (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))
        ).unpair.2 := rfl
  rw [heq, combineFound2_mem_iff hD₀pos hD₀diff hD₀nomin hUnion0 hle0 hle1 hmem0 hmem1 hfound z]
  constructor
  · rintro (⟨hf0, hz⟩ | ⟨hf1, hz⟩)
    · exact Or.inl ((YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n) hf0 z).mp hz)
    · exact Or.inr ((YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hUnion0 (le_refl 1) n (4 ^ n) hf1 z).mp hz)
  · rintro (⟨i, hi, hie, hz⟩ | ⟨i, hi, hie, hz⟩)
    · have hf0 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n)
          ).unpair.1 = 1 :=
        (YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          (Nat.zero_le 1) n (4 ^ n)).mpr ⟨i, hi, hie⟩
      exact Or.inl ⟨hf0, (YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hUnion0 (Nat.zero_le 1) n (4 ^ n) hf0 z).mpr ⟨i, hi, hie, hz⟩⟩
    · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n)
          ).unpair.1 = 1 :=
        (YFoldInner_found_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
          (le_refl 1) n (4 ^ n)).mpr ⟨i, hi, hie⟩
      exact Or.inr ⟨hf1, (YFoldInner_mem_iff P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hUnion0 (le_refl 1) n (4 ^ n) hf1 z).mpr ⟨i, hi, hie, hz⟩⟩

end YPseqCode

end DomainTheory.NeighbourhoodSystems
