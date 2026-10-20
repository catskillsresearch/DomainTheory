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
public import DomainTheory.Neighborhood.Definition79.mem_PDunion

@[expose] public section


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)



/-- **Definition 7.9 — singletons.** Every down-set `↓X` (`X ∈ 𝒟`) is a neighbourhood of `ℙ𝒟`
(the case `n = 1`); these are exactly the neighbourhoods of the prepared system `𝒟†`. -/
theorem PDmem_upSet {X : Set α} (hX : V.mem X) : V.PDmem (V.upSet X) := by
  refine ⟨[X], ?_, ?_⟩
  · intro Y hY; rw [List.mem_singleton] at hY; subst hY; exact hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro hz; exact ⟨X, List.mem_singleton.mpr rfl, hz⟩
    · rintro ⟨Y, hY, hz⟩; rw [List.mem_singleton] at hY; subst hY; exact hz

end NeighborhoodSystem
end DomainTheory.Neighborhood
