/-ai
The inverse of the code-level domain isomorphism is a computable map from the second presentation to the first.

The argument mirrors the forward computability proof with the presentations and the sequence codes exchanged. Pairing projections with the primitive-recursive YPseqCode makes equality of the first enumeration recursively decidable, and a pairing of projections makes inclusion of the second enumeration recursively decidable. Their conjunction is recursively enumerable, the outer quantifier is projected away, and unpacking the paired witness matches the relation criterion for the inverse translation.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.domainIsoCode812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.toD0Code_rel_iff

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DomainIsoCode812dSymmIsComputableMap

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
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in
/-- **Exercise 8.12(d)(5)(f)(iv), the last of the four `(f)` sub-parts.** `ofIso
domainIsoCode812d.symm` is computable relative to `P₁`/`P₀`, the exact mirror of `(f)(ii)`'s
`domainIsoCode812d_isComputableMap` via `(f)(iii)`'s `toD0Code_rel_iff`, swapping `P₀`↔`P₁` and
`XPseqCode`↔`YPseqCode`/`primrec_YPseqCode` throughout: `P₀.eq_computable` reindexed along the
primitive-recursive `YPseqCode` supplies the equality conjunct, `P₁.incl_computable` reindexed
directly supplies the inclusion conjunct, `RecDecidable.and`/`.re`/`REPred.proj` close the outer
`∃ k`, and `REPred.of_iff` matches the exact `IsComputableMap P₁ P₀` shape via `toD0Code_rel_iff`.
Completes `8.12(d)(5)(f)` — hence `8.12(d)(5)` — in full. -/
theorem domainIsoCode812d_symm_isComputableMap :
    IsComputableMap P₁ P₀ (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
      hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
      hUnion1 hX0 hY0).symm) := by
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2
      (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 w.unpair.1)) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      ((primrec_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
        Nat.Primrec.left)
  have hh : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hA : RecDecidable (fun w : ℕ => P₀.X w.unpair.2.unpair.2 =
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 w.unpair.1)) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₀.eq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hB : RecDecidable (fun w : ℕ => P₁.X w.unpair.2.unpair.1 ⊆ P₁.X w.unpair.1) := by
    refine RecDecidable.of_iff (fun w => ?_) (P₁.incl_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) (hA.and hB).re.proj
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).rel (P₁.X t.unpair.1) (P₀.X t.unpair.2) ↔ _
  rw [toD0Code_rel_iff]
  constructor
  · rintro ⟨k, hk, hsub⟩
    exact ⟨k, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hk, hsub⟩⟩
  · rintro ⟨k, hk⟩
    simp only [unpair_pair_fst, unpair_pair_snd] at hk
    exact ⟨k, hk.1, hk.2⟩

end DomainIsoCode812dSymmIsComputableMap

end DomainTheory.NeighbourhoodSystems
