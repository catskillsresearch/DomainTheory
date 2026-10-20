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
public import DomainTheory.Neighborhood.Theorem86.isProjection_subApprox

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6


















/-- **Theorem 8.6(b), in full.** `subApprox` is a finitary projection on `(E → E)`. -/
theorem isFinitaryProjection_subApprox : IsFinitaryProjection (subApprox (E := E)) :=
  ⟨isProjection_subApprox, isFinitary_subApprox⟩

end Sub8_6
end DomainTheory.Neighborhood
