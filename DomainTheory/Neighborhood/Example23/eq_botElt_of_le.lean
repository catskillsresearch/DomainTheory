/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23.Basic


namespace DomainTheory.Neighborhood.Example23

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB







/-- **`⊥` is the unique common lower bound of `true` and `false`.** Any `a : |𝒯|` approximated by
*both* total elements is `⊥` — `𝒯`'s flatness. (Exercise 2.16's uniqueness argument: reading no
tokens yet is the only state consistent with committing to either verdict.) -/
theorem eq_botElt_of_le {a : T.Element} (h0 : a ≤ trueElt) (h1 : a ≤ falseElt) : a = botElt :=
  Example12.neighborhoodSystem.eq_bot_of_le_elemZero_of_le_elemOne h0 h1

end DomainTheory.Neighborhood.Example23
