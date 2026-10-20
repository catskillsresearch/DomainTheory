/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Exercise622.Basic
import DomainTheory.Neighborhood.Exercise622.NStarExpr_rooted


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise619









/-- **`N* ≅ N ⊕ (N ⊗ N*)` has a solution** for any rooted datum domain `N` (the strict streams over
`N`). -/
theorem NStar_eq_solution (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem (NStarExpr N) (NStarExpr_rooted hN)

end Exercise619
end DomainTheory.Neighborhood
