/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import DomainTheory.Neighborhood.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Definition79.Basic
public import DomainTheory.Neighborhood.Definition79.PDmem_upSet

@[expose] public section


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)



/-- **Definition 7.9 — the master neighbourhood `↓Δ`.** The largest neighbourhood of `ℙ𝒟` is
`↓Δ = 𝒟` (all `𝒟`-neighbourhoods), itself a finite union (the case `X₀ = Δ`). -/
theorem PDmem_master : V.PDmem (V.upSet V.master) := V.PDmem_upSet V.master_mem

end NeighborhoodSystem
end DomainTheory.Neighborhood
