/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Theorem51.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51




/-- **Theorem 5.1, tuple case (Scott 1981, PRG-19).** If `⟦σ₀⟧, ⟦σ₁⟧` are approximable, so is the
tuple `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired`, with value `⟨σ₀(w), σ₁(w)⟩`. -/
theorem tuple_apply (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) :=
  toElementMap_paired f g w

end Theorem51
end DomainTheory.Neighborhood
