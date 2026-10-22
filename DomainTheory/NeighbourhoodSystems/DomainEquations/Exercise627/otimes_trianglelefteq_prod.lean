module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.otimesTok_subsystem_prodTok

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


/-- **Exercise 6.27 (1).** `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)`. -/
theorem otimes_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ⊴ prodTok D₀ D₁ :=
  (otimesTok_subsystem_prodTok D₀ D₁).trianglelefteq

end Exercise627
end DomainTheory.NeighbourhoodSystems
