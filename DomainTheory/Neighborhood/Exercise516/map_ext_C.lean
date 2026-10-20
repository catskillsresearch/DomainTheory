/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise419
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise516.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}

/-- Two approximable maps out of `C` agree as soon as they agree on every finite element `σ⊥` and
`σ` (Exercise 2.8). This is the workhorse for the map equalities below. -/
theorem map_ext_C {V : NeighborhoodSystem β} {f g : ApproximableMap C V}
    (hbot : ∀ σ, f.toElementMap (strBot σ) = g.toElementMap (strBot σ))
    (helem : ∀ σ, f.toElementMap (strElem σ) = g.toElementMap (strElem σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (C_mem.mp hX)
  · exact hbot σ
  · exact helem σ

end DomainTheory.Neighborhood.Exercise516
