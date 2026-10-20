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


namespace DomainTheory.Neighborhood

namespace Cofinite

open NeighborhoodSystem














/-- Every filter is `⊑ ofExcluded ℕ` (the whole family `𝒟`; every cofinite `Y` has `Yᶜ ⊆ ℕ`). -/
theorem le_ofExcluded_univ (x : cofiniteSystem.Element) :
    x ≤ ofExcluded Set.univ := by
  intro Y hY
  exact ⟨x.sub hY, Set.subset_univ _⟩

end Cofinite
end DomainTheory.Neighborhood
