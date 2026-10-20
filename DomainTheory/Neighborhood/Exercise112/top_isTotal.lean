/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise112.Basic
public import DomainTheory.Neighborhood.Exercise112.le_top

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise112

open DomainTheory.Neighborhood NeighborhoodSystem















/-- `top` is a total (maximal) element. -/
theorem top_isTotal : neighborhoodSystem.IsTotal top :=
  fun y _ => le_top y

end DomainTheory.Neighborhood.Exercise112
