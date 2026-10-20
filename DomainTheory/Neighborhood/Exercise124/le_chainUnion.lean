/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Order.Zorn
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise124.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- Every member of the chain approximates the union `⋃ C`. -/
theorem le_chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {x : V.Element} (hx : x ∈ C) : x ≤ V.chainUnion C hne hchain :=
  fun _ hX => ⟨x, hx, hX⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
