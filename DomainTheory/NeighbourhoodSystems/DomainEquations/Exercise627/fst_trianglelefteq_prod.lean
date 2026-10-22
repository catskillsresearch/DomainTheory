module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstProj_comp_fstInj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstInj_comp_fstProj_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


/-- **Exercise 6.27 (2).** `𝒟 ⊴ 𝒟 × ℰ`. -/
theorem fst_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    D₀ ⊴ prodTok D₀ D₁ :=
  trianglelefteq_of_projectionPair (fstInj D₀ D₁) (fstProj D₀ D₁)
    (fstProj_comp_fstInj D₀ D₁) (fstInj_comp_fstProj_le D₀ D₁)

end Exercise627
end DomainTheory.NeighbourhoodSystems
