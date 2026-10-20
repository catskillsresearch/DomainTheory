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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`xStepG`'s two split-side outputs reunion to exactly its own input `B`**: from `SplitSpec'`'s
unconditional `(split A B Xn).1 ∪ (split A B Xn).2 = B` field, applied directly (no `.swap`, unlike
`yStepG_fst_union`'s use of the same field). Needed for **8.12(d)(4)(d)(i)**'s one-step 4-way
reunion (the `D₁`-side mirror of `yStepG_fst_union`'s `b2`-level half). -/
theorem xStepG_snd_union {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α) :
    (xStepG splitX A B Xn true).2 ∪ (xStepG splitX A B Xn false).2 = B := by
  have hspec := hxSplit hAB hBmem Xn
  simp only [xStepG, xyStep]
  exact hspec.2.2.2.2.1

end StepGen

end DomainTheory.NeighbourhoodSystems
