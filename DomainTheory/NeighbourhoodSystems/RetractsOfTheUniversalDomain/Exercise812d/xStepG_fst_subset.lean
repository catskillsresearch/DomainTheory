/-ai
The first component of a generalized X-step is contained in the parent first set.

If the bit is true, the step intersects with the neighbourhood, and an intersection is contained in its left factor. If the bit is false, the step takes a difference, which is contained in the set being cut.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

theorem xStepG_fst_subset (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStepG splitX A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, ite_true]; exact Set.inter_subset_left
  · simp only [xStepG, xyStep, hb]; exact Set.sdiff_subset

end StepGen

end DomainTheory.NeighbourhoodSystems
