/-ai
If a neighbourhood belongs to the code-level pushforward of an element x, a second neighbourhood of the second system is genuine, and the first is contained in the second, then the second belongs to the pushforward.

Write the first neighbourhood as the basic neighbourhood of an X-sequence code i that x meets. Surjectivity names the second as a basic neighbourhood of some index k. The cross-parity inclusion turns the containment into an inclusion of the basic neighbourhood of i in the basic neighbourhood of the Y-sequence code of k, and upward closure of x, using that every such code is genuine, puts x there. The reverse of the cross-parity equality at that Y-sequence code and k shows that this basic neighbourhood is the X-sequence code of that index.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode_mem_unconditional
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.X_subset_YPseqCode_iff_XPseqCode_subset_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode_eq_Y_iff_X_eq_YPseqCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section ToD1CodeUpMem

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(d)(i).** The standalone `up_mem` obligation for `toD1Code`'s membership
predicate `fun T => ∃ n, T = P₁.X (XPseqCode … n) ∧ x.mem (P₀.X n)`, stated at the exact type
`Element.up_mem` needs so it plugs directly into the final structure literal. Code-level analogue
of `Exercise812c.lean`'s `toD1.up_mem`, but needing only **one** `surj` call (not two): `P₁.surj`
names the arbitrary target `T2` as some `P₁.X k`; `(d)(5)(c)(i)`'s cross-parity order fact then
transports `x.mem (P₀.X i)` across to `x.mem (P₀.X (YPseqCode … k))` — already literally
`x.mem (P₀.X j)` for the explicit witness `j := YPseqCode … k`, no further covering search needed;
`(d)(5)(c)(iii)`'s `XPseqCode_eq_Y_iff_X_eq_YPseqCode`, applied at the self-referential pair
`(YPseqCode … k, k)` whose "other side" is `rfl`, supplies the closing index equation for free. -/
theorem toD1Code_up_mem (x : D₀.Element) {T1 T2 : Set β}
    (h1 : ∃ n, T1 = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
      x.mem (P₀.X n))
    (hD1T2 : D₁.mem T2) (hT1T2 : T1 ⊆ T2) :
    ∃ n, T2 = P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) ∧
      x.mem (P₀.X n) := by
  obtain ⟨i, rfl, hxi⟩ := h1
  obtain ⟨k, hk⟩ := P₁.surj hD1T2
  subst hk
  have hsub : P₀.X i ⊆
      P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) :=
    (X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i k).mpr hT1T2
  have hxYk :
      x.mem (P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k)) :=
    x.up_mem hxi
      (YPseqCode_mem_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 k)
      hsub
  refine ⟨YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k, ?_, hxYk⟩
  exact ((XPseqCode_eq_Y_iff_X_eq_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
    (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) k).mpr rfl).symm

end ToD1CodeUpMem

end DomainTheory.NeighbourhoodSystems
