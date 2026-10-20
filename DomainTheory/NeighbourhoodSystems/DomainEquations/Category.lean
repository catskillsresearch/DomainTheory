/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-!
The category of domains is Mathlib's `CategoryTheory.Category`. Scott writes composition as
"`g` after `f`"; Mathlib writes `f ≫ g` for "`f` then `g`". The notation `g ⊚ f` is that reversed
reading, so `g ⊚ f` is `f ≫ g`.
-/

export CategoryTheory (Category)

open scoped CategoryTheory

universe u v

scoped notation "𝟙" => CategoryTheory.CategoryStruct.id

abbrev compAfter {Obj : Type u} [Category.{v} Obj] {X Y Z : Obj} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
  f ≫ g

scoped infixr:80 " ⊚ " => compAfter

end DomainTheory.NeighbourhoodSystems
