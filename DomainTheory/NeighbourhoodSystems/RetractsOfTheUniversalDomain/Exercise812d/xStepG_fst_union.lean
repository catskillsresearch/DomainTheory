module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **`xStepG`'s two direct-refine outputs reunion to exactly the parent**: the trivial two-set
identity `(A ∩ Xn) ∪ (A \ Xn) = A`, restated through `xStepG`'s `.1`. Needed for
**8.12(d)(4)(c)(i)**'s one-step 4-way reunion (the `b1`-level half of the argument); no `SplitSpec'`
hypotheses needed at all, unlike every other fact about `xStepG`/`yStepG` in this section. -/
theorem xStepG_fst_union (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) :
    (xStepG splitX A B Xn true).1 ∪ (xStepG splitX A B Xn false).1 = A := by
  simp only [xStepG, xyStep]
  exact Set.inter_union_sdiff A Xn

end StepGen

end DomainTheory.NeighbourhoodSystems
