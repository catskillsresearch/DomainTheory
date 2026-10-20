module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toElementMap_inclMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toElementMap_strctMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct_incl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.ext_of_principal

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










theorem strctMap_comp_inclMap :
    (strctMap (V₀ := V₀) (V₁ := V₁)).comp inclMap = idMap (strictFun V₀ V₁) := by
  apply ext_of_principal
  intro X hX
  rw [toElementMap_comp, toElementMap_inclMap, toElementMap_strctMap, strct_incl, toElementMap_idMap]

end Part5
end Exercise627
end DomainTheory.NeighbourhoodSystems
