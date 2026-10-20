/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
