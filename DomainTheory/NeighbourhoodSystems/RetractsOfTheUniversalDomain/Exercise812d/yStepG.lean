/-ai
The generalized Y-step splits the first neighbourhood system by an abstract split and refines the second system directly. It is the component swap of the joint step on the swapped arguments.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section StepGen

variable {α β : Type*}

/-- **Generalized `yStep`**: split `D₀`'s side (via the abstract `splitY`) while directly refining
`D₁`'s side. Literally `(xyStep splitY _ _ _ _).swap`; `yStep D₀ hD₀nomin = yStepG (splitChoice' D₀
hD₀nomin)`. -/
noncomputable def yStepG (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep splitY B1 A1 Yn b).swap

end StepGen

end DomainTheory.NeighbourhoodSystems
