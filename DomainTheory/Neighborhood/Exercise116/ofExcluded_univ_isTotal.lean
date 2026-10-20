/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise116.Basic
import DomainTheory.Neighborhood.Exercise116.le_ofExcluded_univ


namespace DomainTheory.Neighborhood

namespace Cofinite

open NeighborhoodSystem














/-- **Exercise 1.16 — the unique total element.** `ofExcluded ℕ` (matching the greatest
element `ℕ ∈ 𝒫(ℕ)`) is total: it is `⊑`-maximal. -/
theorem ofExcluded_univ_isTotal : cofiniteSystem.IsTotal (ofExcluded Set.univ) :=
  fun y _ => le_ofExcluded_univ y

end Cofinite
end DomainTheory.Neighborhood
