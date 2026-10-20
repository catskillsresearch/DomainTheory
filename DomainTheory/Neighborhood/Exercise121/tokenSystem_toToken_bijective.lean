/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem110
import DomainTheory.Neighborhood.Exercise121.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)




/-- **Exercise 1.21 — tokens ↔ elements.** `toToken : |𝒟| → |{[X]}|` is a bijection (it is the
underlying map of the order-iso `tokenIso`), so a complete system identifies tokens with
(partial) elements under a one-one correspondence. -/
theorem tokenSystem_toToken_bijective : Function.Bijective V.toToken :=
  V.tokenIso.bijective

end NeighborhoodSystem
end DomainTheory.Neighborhood
