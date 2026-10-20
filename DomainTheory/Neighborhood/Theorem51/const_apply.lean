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



/-- **Theorem 5.1, constant case (Scott 1981, PRG-19).** A constant `k` is interpreted by the
constant map, which is approximable with value `k`. -/
theorem const_apply (k : V₁.Element) (x : V₀.Element) :
    (constMap V₀ k).toElementMap x = k := toElementMap_constMap k x

end Theorem51
end DomainTheory.Neighborhood
