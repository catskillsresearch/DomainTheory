/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Example23
public import DomainTheory.Neighborhood.Theorem75
public import DomainTheory.Neighborhood.Exercise724.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise724

open NeighborhoodSystem Domain.Recursive










































































/-- **Exercise 7.24 (i) — `L` is effectively given.** -/
theorem L_isEffectivelyGiven : L.IsEffectivelyGiven := ⟨Lpres⟩

end DomainTheory.Neighborhood.Exercise724
