/-ai
The image of XPseqCode at depth 0 is the master neighbourhood of the second neighbourhood system, assuming the zero codes name the two masters.

The depth-zero atom-pair state is not junk and indexes both masters. The half-step atom at bit-source 0 is not junk, because otherwise the emptiness test would say that the master meets itself emptily. Its index is the positive split index of those two masters against the master, and the split specification, using that the master differs from itself by the empty set, says that this positive piece is the second master. Antisymmetry uses the unconditional membership criterion: every point of the code lies in some non-junk atom and hence in the master, and every master point lies in the atom at index 0.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.mem_XPseqCode_iff_unconditional
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_zero

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XYPseqCodeZero

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hX0 in
/-- **8.12(d)(5)(a), `X`-side.** `P₁.X (XPseqCode … 0) = D₁.master`. -/
theorem XPseqCode_zero :
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 0) = D₁.master := by
  have hjunk0 := atomPairJunk_zero P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0
  have hcs := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne 0 0 hjunk0
  have hA0 : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₀.master := hcs.1
  have hB0 : P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := hcs.2
  have hxjunk0 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 = 0 := by
    rw [xPseqAtomJunk_eq, hjunk0, selectFn_zero]
    by_contra hcon
    have hle := emptyInterDec_le_one P₀ (Nat.pair
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0)
    have h1 : emptyInterDec P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0) = 1 := by omega
    have hempty := (emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1
    rw [hA0, hX0, Set.inter_self] at hempty
    exact hD₀mne.ne_empty hempty
  have hidxeq : xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0 =
      hSplitX.posIdx (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 :=
    xPseqAtomIdx_eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxjunk0
  have hAB1 : D₀.master = ∅ ↔ D₁.master = ∅ :=
    ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  have hBE1 : D₁.master = ∅ ∨ D₁.mem D₁.master := Or.inr D₁.master_mem
  have hspec1 := hxSplit hAB1 hBE1 D₀.master
  have hdiff1 : D₀.master \ D₀.master = ∅ := Set.sdiff_self
  have h2empty1 : (splitX D₀.master D₁.master D₀.master).2 = ∅ := hspec1.2.2.2.1.mp hdiff1
  have hunion1 : (splitX D₀.master D₁.master D₀.master).1 = D₁.master := by
    have hu := hspec1.2.2.2.2.1
    rwa [h2empty1, Set.union_empty] at hu
  have hne1 : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0))
      (P₀.X 0)).1 ≠ ∅ := by rw [hA0, hB0, hX0, hunion1]; exact hD₁mne.ne_empty
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) 0 hne1
  rw [hA0, hB0, hX0] at hposspec
  have hzeroeq : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 0) =
      D₁.master := by rw [hidxeq, ← hposspec]; exact hunion1
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i, -, -, hzi⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX
      splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
      hUnion1 0 z).mp hz
    exact D₁.sub_master (xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i) hzi
  · intro z hz
    refine (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 0
      z).mpr ⟨0, by norm_num, hxjunk0, ?_⟩
    rwa [hzeroeq]

end XYPseqCodeZero

end DomainTheory.NeighbourhoodSystems
