/-ai
Diagrammatic composition sends a morphism from Y to Z and a morphism from X to Y to their categorical composite from X to Z.
ai-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

export CategoryTheory (Category)

open scoped CategoryTheory

universe u

abbrev compAfter {Obj : Type u} [Category.{v} Obj] {X Y Z : Obj} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
  f ≫ g

end DomainTheory.NeighbourhoodSystems
