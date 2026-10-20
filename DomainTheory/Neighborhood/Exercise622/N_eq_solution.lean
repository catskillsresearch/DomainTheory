/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Exercise622.Basic
import DomainTheory.Neighborhood.Exercise622.NExpr_rooted


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise619









/-- **`N ≅ {{0},{0,Λ}} ⊕ N` has a solution.** There is `Γ` (the vertical naturals' token set) with
`Γ = tok(NExpr({Γ}))`, so `{Γ} ◁ NExpr({Γ})` and Theorem 6.14 applies. -/
theorem N_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (NExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem NExpr NExpr_rooted

end Exercise619
end DomainTheory.Neighborhood
