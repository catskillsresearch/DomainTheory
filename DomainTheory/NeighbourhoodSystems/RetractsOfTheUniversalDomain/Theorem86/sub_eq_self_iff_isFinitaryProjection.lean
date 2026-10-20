/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem85
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise213
public import DomainTheory.Neighborhood.Proposition611
public import DomainTheory.Neighborhood.Theorem86.Basic
public import DomainTheory.Neighborhood.Theorem86.isFinitaryProjection_of_sub_eq_self
public import DomainTheory.Neighborhood.Theorem86.sub_eq_self_of_isFinitaryProjection

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **Theorem 8.6's range characterization, in full.** `sub f = f ↔ f` is a finitary projection. -/
theorem sub_eq_self_iff_isFinitaryProjection {f : ApproximableMap E E} :
    sub f = f ↔ IsFinitaryProjection f :=
  ⟨isFinitaryProjection_of_sub_eq_self, sub_eq_self_of_isFinitaryProjection⟩

end DomainTheory.Neighborhood
