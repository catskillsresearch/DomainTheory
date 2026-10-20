/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.mem_union_of_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk_zero_or_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldStep_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner_found_le_one

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
/-- **Once "found", the running union's code is always `D₀`-genuine.** Exactly mirrors
`XFold_mem_of_found`, with `hUnion0`/`D₀` in place of `hUnion1`/`D₁`. -/
theorem YFoldInner_mem_of_found {bx : ℕ} (hbx : bx ≤ 1) (n : ℕ) :
    ∀ N, (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1 = 1
      → D₀.mem (P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        n bx N).unpair.2) := by
  intro N
  induction N with
  | zero => intro h; simp [YFoldInner_zero] at h
  | succ N ih =>
    intro hfound1
    rw [YFoldInner_succ, YFoldStep_eq] at hfound1 ⊢
    rcases yPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hbx n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := YFoldInner_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        hbx n N
      rcases Nat.eq_zero_or_pos
          (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N).unpair.1
        with hf0 | hfpos
      · rw [show (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
          ).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        exact yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
      · have hf1 : (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
            ).unpair.1 = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := ih hf1
        have hnewmem := yPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx
        have hex : ∃ k, P₀.X k =
            P₀.X (YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n bx N
              ).unpair.2 ∪
              P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N bx) :=
          P₀.surj (NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem)
        rw [hUnion0.unionIdx_spec hex]
        exact NeighborhoodSystem.mem_union_of_mem hD₀pos hD₀diff hD₀nomin hprevmem hnewmem
    · rw [h1, selectFn_one] at hfound1 ⊢
      exact ih hfound1

end YPseqCode

end DomainTheory.NeighbourhoodSystems
