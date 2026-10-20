/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise120.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)












/-- **Exercise 1.20 (statement).** `𝒟` and its power system `𝒟'` are isomorphic. -/
theorem isomorphic_powerSystem : V ≅ᴰ V.powerSystem := ⟨V.powerIso⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
