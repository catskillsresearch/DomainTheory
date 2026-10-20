/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Example12.Basic
import DomainTheory.Neighborhood.Example12.element_classification


namespace DomainTheory.Neighborhood.Example12























namespace neighborhoodSystem

open NeighborhoodSystem






theorem bot_is_unique_partial (x : neighborhoodSystem.Element) :
    x ≠ elemZero → x ≠ elemOne → x = bot := by
  intro hne0 hne1
  rcases element_classification x with hx | hx | hx
  · exact hx
  · exact (hne0 hx).elim
  · exact (hne1 hx).elim

end neighborhoodSystem
end DomainTheory.Neighborhood.Example12
