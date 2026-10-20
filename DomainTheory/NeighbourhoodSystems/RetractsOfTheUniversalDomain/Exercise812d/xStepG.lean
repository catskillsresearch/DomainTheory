module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **Generalized `xStep`**: split `D₁`'s side (via the abstract `splitX`) while directly refining
`D₀`'s side. Literally `xyStep splitX`; `xStep D₁ hD₁nomin = xStepG (splitChoice' D₁ hD₁nomin)`. -/
noncomputable def xStepG (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep splitX A B Xn b

end StepGen

end DomainTheory.NeighbourhoodSystems
