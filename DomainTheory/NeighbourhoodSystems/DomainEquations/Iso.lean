/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- An isomorphism in the category: a pair of mutually inverse morphisms. -/
structure Iso (X Y : Obj) where
  /-- The forward morphism. -/
  hom : Category.Hom X Y
  /-- The inverse morphism. -/
  inv : Category.Hom Y X
  /-- `inv ∘ hom = I_X`. -/
  hom_inv_id : inv ⊚ hom = Category.id X
  /-- `hom ∘ inv = I_Y`. -/
  inv_hom_id : hom ⊚ inv = Category.id Y

end DomainTheory.NeighbourhoodSystems
