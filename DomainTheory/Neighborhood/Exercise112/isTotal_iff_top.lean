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
public import DomainTheory.Neighborhood.Exercise112.top_isTotal

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise112

open DomainTheory.Neighborhood NeighborhoodSystem















/-- `top` is the **unique** total element: an element is total iff it equals `top`. -/
theorem isTotal_iff_top (x : neighborhoodSystem.Element) :
    neighborhoodSystem.IsTotal x ↔ x = top := by
  constructor
  · intro h
    exact le_antisymm (le_top x) (h top (le_top x))
  · rintro rfl; exact top_isTotal

end DomainTheory.Neighborhood.Exercise112
