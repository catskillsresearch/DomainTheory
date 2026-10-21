/-ai
An isomorphism from an object X to an object Y consists of a morphism from X to Y, a morphism from Y to X, and the two equations saying that the two composites are the identity morphisms of X and of Y.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor

@[expose] public section

universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- An isomorphism in the category: a pair of mutually inverse morphisms. -/
structure Iso (X Y : Obj) where
  /-- The forward morphism. -/
  hom : (X ⟶ Y)
  /-- The inverse morphism. -/
  inv : (Y ⟶ X)
  /-- `inv ∘ hom = I_X`. -/
  hom_inv_id : inv ⊚ hom = (𝟙 X)
  /-- `hom ∘ inv = I_Y`. -/
  inv_hom_id : hom ⊚ inv = (𝟙 Y)

end DomainTheory.NeighbourhoodSystems
