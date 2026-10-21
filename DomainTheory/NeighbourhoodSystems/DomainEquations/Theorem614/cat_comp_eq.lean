/-ai
Composition of morphisms in the category of domains is composition of the underlying approximable maps.

The equality is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}


/-- In the category of domains, `⊚` (categorical composition) is `ApproximableMap.comp`. -/
theorem cat_comp_eq {X Y Z : DomainObj} (g : (Y ⟶ Z)) (f : (X ⟶ Y)) :
    g ⊚ f = g.comp f := rfl

end Theorem614
end DomainTheory.NeighbourhoodSystems
