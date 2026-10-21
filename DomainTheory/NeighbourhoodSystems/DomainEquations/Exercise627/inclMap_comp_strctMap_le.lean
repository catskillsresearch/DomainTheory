/-ai
The composite of inclusion after strictification lies below the identity on the function space.

The element-map form of the inequality reduces the composite to inclusion of the strictification of an arbitrary element, and that element lies below the original.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toElementMap_inclMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toElementMap_strctMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl_strct_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

















section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










theorem inclMap_comp_strctMap_le :
    (inclMap (V₀ := V₀) (V₁ := V₁)).comp strctMap ≤ idMap (funSpace V₀ V₁) := by
  rw [le_iff_toElementMap_le]
  intro ψ
  rw [toElementMap_comp, toElementMap_strctMap, toElementMap_inclMap, toElementMap_idMap]
  exact incl_strct_le ψ

end Part5
end Exercise627
end DomainTheory.NeighbourhoodSystems
