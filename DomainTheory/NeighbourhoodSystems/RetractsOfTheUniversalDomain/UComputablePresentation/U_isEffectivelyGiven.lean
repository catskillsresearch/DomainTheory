/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.IntervalPrimrec
public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.UComputablePresentation.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem














































/-- **`𝒰` is effectively given.** -/
theorem U_isEffectivelyGiven : U.IsEffectivelyGiven := ⟨UComputablePresentation⟩

end DomainTheory.Neighborhood
