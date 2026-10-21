/-ai
The composite of the first-factor injection after the first-factor projection lies below the identity on the product.

A composite relation supplies an intermediate neighbourhood of D₀ and two inclusions of product neighbourhoods. The composite of those inclusions, together with the two product memberships, is the identity relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}





theorem fstInj_comp_fstProj_le (D₀ D₁ : NeighborhoodSystem Str) :
    (fstInj D₀ D₁).comp (fstProj D₀ D₁) ≤ idMap (prodTok D₀ D₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

end Exercise627
end DomainTheory.NeighbourhoodSystems
