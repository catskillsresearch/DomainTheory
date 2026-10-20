/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation4
public import DomainTheory.NeighbourhoodSystems.DomainEquations.compAfter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category.notation6

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




end DomainTheory.NeighbourhoodSystems
