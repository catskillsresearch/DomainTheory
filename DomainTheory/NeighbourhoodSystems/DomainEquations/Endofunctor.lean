/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
  map : {X Y : Obj} → Category.Hom X Y → Category.Hom (obj X) (obj Y)
  /-- `T(I_X) = I_{T(X)}`. -/
  map_id : ∀ (X : Obj), map (Category.id X) = Category.id (obj X)
  /-- `T(g ∘ f) = T(g) ∘ T(f)`. -/
  map_comp : ∀ {X Y Z : Obj} (g : Category.Hom Y Z) (f : Category.Hom X Y),
    map (g ⊚ f) = (map g) ⊚ (map f)

end DomainTheory.NeighbourhoodSystems
