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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk_zero_or_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFoldStep_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold_found_le_one

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

include hD₁pos hD₁diff hD₁nomin in
/-- **Once "found", the running union's code is always `D₁`-genuine.** New content beyond
`Theorem88d.lean`'s precedent (there, `unionUX`'s output is unconditionally genuine, since `U` is
unconditionally union-closed): here `hUnion1.unionIdx_spec`'s conclusion is conditional on its
existential hypothesis, discharged at each step via `(d)(4)(b)`'s `mem_union_of_mem` applied to the
running union (genuine, by this very induction) and the new atom (genuine, `xPseqAtomIdx_mem`,
unconditionally). This is exactly the fact `XFold_mem_iff` below needs to legally rewrite through
`unionIdx_spec` at its own inductive step. -/
theorem XFold_mem_of_found (n : ℕ) :
    ∀ N, (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 = 1 →
      D₁.mem (P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2) := by
  intro N
  induction N with
  | zero => intro h; simp [XFold_zero] at h
  | succ N ih =>
    intro hfound1
    rw [XFold_succ, XFoldStep_eq] at hfound1 ⊢
    rcases xPseqAtomJunk_zero_or_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N with
      h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      have hle := XFold_found_le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N
      rcases Nat.eq_zero_or_pos
          (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1 with
        hf0 | hfpos
      · rw [show (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
          = 0 from hf0, selectFn_zero, unpair_pair_snd]
        exact xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
      · have hf1 : (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.1
            = 1 := by omega
        rw [hf1, selectFn_one, unpair_pair_snd]
        have hprevmem := ih hf1
        have hnewmem := xPseqAtomIdx_mem P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N
        have hex : ∃ k, P₁.X k =
            P₁.X (XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n N).unpair.2 ∪
              P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n N) :=
          P₁.surj (NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem)
        rw [hUnion1.unionIdx_spec hex]
        exact NeighborhoodSystem.mem_union_of_mem hD₁pos hD₁diff hD₁nomin hprevmem hnewmem
    · rw [h1, selectFn_one] at hfound1 ⊢
      exact ih hfound1

end XPseqCode

end DomainTheory.NeighbourhoodSystems
