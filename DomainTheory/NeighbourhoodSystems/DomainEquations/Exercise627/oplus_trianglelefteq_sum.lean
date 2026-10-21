/-ai
The coalesced sum embeds as a subdomain of the separated sum.

The coalesced sum is a subsystem of the separated sum, and every subsystem embeds.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplusTok_subsystem_sumTok

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.27 (3).** `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)`. -/
theorem oplus_trianglelefteq_sum (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ⊴ sumTok D₀ D₁ h₀ h₁ :=
  (oplusTok_subsystem_sumTok h₀ h₁).trianglelefteq

end Exercise627
end DomainTheory.NeighbourhoodSystems
