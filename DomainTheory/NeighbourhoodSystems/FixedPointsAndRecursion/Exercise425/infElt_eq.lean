/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise425.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise425

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap



























/-- `1^∞ = 1·1^∞`: the infinite sequence is fixed by the successor. -/
theorem infElt_eq : consMap.toElementMap infElt = infElt :=
  toElementMap_fixElement consMap

end DomainTheory.Neighborhood.Exercise425
