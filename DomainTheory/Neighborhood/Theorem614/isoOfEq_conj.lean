/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem614.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}













































/-- Conjugation by the identity isomorphism `isoOfEq e` is the object-transport along `e`. -/
theorem isoOfEq_conj {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : Category.Hom X X) :
    (isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = (e ▸ f : Category.Hom Y Y) := by
  cases e
  change Category.id X ⊚ f ⊚ Category.id X = f
  rw [Category.id_comp, Category.comp_id]

end Theorem614
end DomainTheory.Neighborhood
