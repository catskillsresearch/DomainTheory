/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Theorem110.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)














/-- **Theorem 1.10 (statement).** Any neighbourhood system is isomorphic to its element-token
system: `𝒟 ≅ᴰ {[X]}`. -/
theorem isomorphic_tokenSystem : V ≅ᴰ V.tokenSystem := ⟨V.tokenIso⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
