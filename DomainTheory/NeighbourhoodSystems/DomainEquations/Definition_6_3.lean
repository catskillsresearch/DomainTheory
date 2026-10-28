module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_28

@[expose] public section

section
universe u
namespace DomainTheory.NeighbourhoodSystems
variable {Obj : Type u} [Category Obj]

structure Endofunctor (Obj : Type u) [Category Obj] where

  obj : Obj → Obj

  map : {X Y : Obj} → (X ⟶ Y) → ((obj X) ⟶ (obj Y))

  map_id : ∀ (X : Obj), map ((𝟙 X)) = (𝟙 (obj X))

  map_comp : ∀ {X Y Z : Obj} (g : (Y ⟶ Z)) (f : (X ⟶ Y)),
    map (g ⊚ f) = (map g) ⊚ (map f)

end DomainTheory.NeighbourhoodSystems
end

section

universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

structure Iso (X Y : Obj) where

  hom : (X ⟶ Y)

  inv : (Y ⟶ X)

  hom_inv_id : inv ⊚ hom = (𝟙 X)

  inv_hom_id : hom ⊚ inv = (𝟙 Y)

end DomainTheory.NeighbourhoodSystems
end
