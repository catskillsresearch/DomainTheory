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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_fst_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG_fst_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)

include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **8.12(d)(4)(c)(i): the one-step 4-way classical reunion.** Ranging over all four
`(b1, b2) : Bool × Bool` sign choices at depth `n`, the resulting depth-`(n+1)` `D₀`-pieces
reunion to *exactly* the depth-`n` parent's `D₀`-piece — the algebraic core of the covering
argument closing `XPseqCode`'s deferred unconditional-"found" gap (`(d)(4)(c)`'s nested sub-goals).
Two facts chained: `xStepG_fst_union` at the `b1`-level (no hypotheses needed) and `yStepG_fst_union`
at the `b2`-level (needs `xStepG`'s output to satisfy `SplitSpec'`'s preconditions, supplied by the
same case analysis `xStepG_spec` already does, inlined here since `xStepG_spec` itself is hardcoded
to `(δ n).1` rather than a free `b1`). -/
theorem atomPairG_fst_union_step (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) true).2 (Y n) false).1) ∪
    ((yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) true).1 ∪
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) false).2 (Y n) false).1) =
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  have hBAtrue : (xStepG splitX A B (X n) true).2 = ∅ ↔ (xStepG splitX A B (X n) true).1 = ∅ := by
    simp only [xStepG, xyStep, ite_true]; exact hspec1.2.2.1.symm
  have hAmemtrue : (xStepG splitX A B (X n) true).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) true).1 := by
    simp only [xStepG, xyStep, ite_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
  have hBAfalse : (xStepG splitX A B (X n) false).2 = ∅ ↔ (xStepG splitX A B (X n) false).1 = ∅ := by
    simp only [xStepG, xyStep]; exact hspec1.2.2.2.1.symm
  have hAmemfalse : (xStepG splitX A B (X n) false).1 = ∅ ∨ D₀.mem (xStepG splitX A B (X n) false).1 := by
    simp only [xStepG, xyStep]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)
  rw [yStepG_fst_union hySplit hBAtrue hAmemtrue (Y n),
    yStepG_fst_union hySplit hBAfalse hAmemfalse (Y n)]
  exact xStepG_fst_union splitX A B (X n)

end AtomPairGen

end DomainTheory.NeighbourhoodSystems
