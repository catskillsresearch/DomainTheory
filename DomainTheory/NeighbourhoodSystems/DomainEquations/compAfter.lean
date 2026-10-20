module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

export CategoryTheory (Category)

open scoped CategoryTheory

universe u v

abbrev compAfter {Obj : Type u} [Category.{v} Obj] {X Y Z : Obj} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
  f ≫ g

end DomainTheory.NeighbourhoodSystems
