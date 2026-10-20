/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise321.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}







theorem leastStep_mem {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    leastStep Y Z hY hZ ∈ step Y Z := by
  have := leastMap_mem_stepFun (V₀ := V₀) (V₁ := V₁)
    (L := [(Y, Z)]) (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)
  rw [stepFun_singleton] at this
  exact this

end DomainTheory.Neighborhood
