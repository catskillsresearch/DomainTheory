/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Example13.Basic


namespace DomainTheory.Neighborhood.Example13






















namespace neighborhoodSystem

open NeighborhoodSystem







theorem bot_lt_elemTwelve : bot < elemTwelve := by
  constructor
  · intro X hx
    rw [hx]
    exact Or.inl rfl
  · intro h
    have : bot.mem twelve := h twelve (Or.inr rfl)
    exact twelve_ne_master this

end neighborhoodSystem
end DomainTheory.Neighborhood.Example13
