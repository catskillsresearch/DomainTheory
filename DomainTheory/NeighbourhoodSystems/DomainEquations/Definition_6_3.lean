module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_28

@[expose] public section

section
universe u
namespace DomainTheory.NeighbourhoodSystems
variable {Obj : Type u} [Category Obj]
/- concordance: source L3625 DEFINITION 6.3 functor -/
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
end

section
-- Iso.lean
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
end

section
-- TAlgebra.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

end DomainTheory.NeighbourhoodSystems
end
