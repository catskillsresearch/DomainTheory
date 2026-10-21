/-ai
Conjugation of an endomorphism by the identity isomorphism of an object equality equals transport of that endomorphism along the equality.

Cases on the equality reduce both sides to the endomorphism composed with identity morphisms, and the identity laws leave the endomorphism unchanged.
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


/-- Conjugation by the identity isomorphism `isoOfEq e` is the object-transport along `e`. -/
theorem isoOfEq_conj {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : (X ⟶ X)) :
    (isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = (e ▸ f : (Y ⟶ Y)) := by
  cases e
  change (𝟙 X) ⊚ f ⊚ (𝟙 X) = f
  dsimp only [compAfter]
  rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

end Theorem614
end DomainTheory.NeighbourhoodSystems
