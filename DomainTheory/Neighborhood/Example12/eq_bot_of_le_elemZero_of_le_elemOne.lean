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
import DomainTheory.Neighborhood.Example12.not_elemZero_le_elemOne
import DomainTheory.Neighborhood.Example12.not_elemOne_le_elemZero


namespace DomainTheory.Neighborhood.Example12























namespace neighborhoodSystem

open NeighborhoodSystem







/-- **`⊥` is the unique common lower bound of `elemZero` and `elemOne`.** Any element approximated
by *both* total elements is exactly `⊥`: `element_classification` puts it at `bot`, `elemZero`, or
`elemOne`, and the latter two are excluded by incomparability. This is the order-theoretic
ingredient (continuity/flatness of `𝒯`) behind the uniqueness half of Exercise 2.16. -/
theorem eq_bot_of_le_elemZero_of_le_elemOne {a : neighborhoodSystem.Element}
    (h0 : a ≤ elemZero) (h1 : a ≤ elemOne) : a = bot := by
  rcases element_classification a with rfl | rfl | rfl
  · rfl
  · exact absurd h1 not_elemZero_le_elemOne
  · exact absurd h0 not_elemOne_le_elemZero

end neighborhoodSystem
end DomainTheory.Neighborhood.Example12
