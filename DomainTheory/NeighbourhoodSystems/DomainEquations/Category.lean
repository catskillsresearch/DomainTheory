/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

/-- A category: objects (a type `Obj`), hom-sets `Hom X Y`, identities, composition, and the three
category laws. We bundle it as a class so a fixed object type can carry its categorical structure.
The composition `comp g f` reads "`g` after `f`" (the same convention as `ApproximableMap.comp`). -/
class Category (Obj : Type u) where
  /-- The morphisms from `X` to `Y`. -/
  Hom : Obj → Obj → Type v
  /-- The identity morphism on each object. -/
  id : (X : Obj) → Hom X X
  /-- Composition: `comp g f` is "`g` after `f`". -/
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  /-- Left identity law `I ∘ f = f`. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  /-- Right identity law `f ∘ I = f`. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  /-- Associativity `(h ∘ g) ∘ f = h ∘ (g ∘ f)`. -/
  assoc : ∀ {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp (comp h g) f = comp h (comp g f)

@[inherit_doc] infixr:80 " ⊚ " => Category.comp

end DomainTheory.NeighbourhoodSystems
