module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`yStepG`'s two direct-refine outputs reunion to exactly its own input `B1`**: the trivial
two-set identity `(B1 ∩ Yn) ∪ (B1 \ Yn) = B1`, restated through `yStepG`'s `.2` (the `.swap`-ed
direct-refine side, on `D₁`'s side). Needed for **8.12(d)(4)(d)(i)**'s one-step 4-way reunion (the
`D₁`-side mirror of `xStepG_fst_union`'s `b1`-level half); no `SplitSpec'` hypotheses needed, exactly
like `xStepG_fst_union`. -/
theorem yStepG_snd_union (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) :
    (yStepG splitY A1 B1 Yn true).2 ∪ (yStepG splitY A1 B1 Yn false).2 = B1 := by
  simp only [yStepG, xyStep, Prod.swap]
  exact Set.inter_union_sdiff B1 Yn

end StepGen

end DomainTheory.NeighbourhoodSystems
