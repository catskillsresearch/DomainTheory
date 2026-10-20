/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise820.Basic
public import DomainTheory.Neighborhood.Exercise820.trianglelefteq_funSpace_const

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v






variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D→D`.** -/
theorem D_trianglelefteq_funSpace : D ⊴ funSpace D D := trianglelefteq_funSpace_const D D

end DomainTheory.Neighborhood
