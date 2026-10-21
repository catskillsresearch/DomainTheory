/-ai
An endofunctor on a category assigns an object to each object and a morphism between the image objects to each morphism, sends identity morphisms to identity morphisms, and sends a composite to the composite of the images.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

/-- **Definition 6.3 (Scott 1981, PRG-19).** A *functor* on a category into itself (an
*endofunctor*): an assignment `obj` on objects and `map` on morphisms preserving identities
(`map_id`) and composition (`map_comp`). -/
structure Endofunctor (Obj : Type u) [Category Obj] where
  /-- The action on objects. -/
  obj : Obj → Obj
  /-- The action on morphisms. -/
  map : {X Y : Obj} → (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  /-- `T(I_X) = I_{T(X)}`. -/
  map_id : ∀ (X : Obj), map ((𝟙 X)) = (𝟙 (obj X))
  /-- `T(g ∘ f) = T(g) ∘ T(f)`. -/
  map_comp : ∀ {X Y Z : Obj} (g : (Y ⟶ Z)) (f : (X ⟶ Y)),
    map (g ⊚ f) = (map g) ⊚ (map f)

end DomainTheory.NeighbourhoodSystems
