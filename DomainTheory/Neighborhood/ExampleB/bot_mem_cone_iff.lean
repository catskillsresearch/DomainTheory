/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Data.List.Infix
import DomainTheory.Neighborhood.ExampleB.Basic
import DomainTheory.Neighborhood.ExampleB.cone_injective


namespace DomainTheory.Neighborhood.ExampleB

open DomainTheory.Neighborhood NeighborhoodSystem





















/-- **`⊥` sits only in the cone of the empty prefix.** `⊥.mem(σΣ*) ↔ σ = Λ`: `⊥`'s only
neighbourhood is `Δ = ΛΣ*` (`cone_nil`), and a cone determines its prefix (`cone_injective`).
(Used by Exercise 2.17's base case, where `g(1)=⊥` is stated only at the input `⊥`.) -/
theorem bot_mem_cone_iff {σ : Str} : B.bot.mem (cone σ) ↔ σ = [] := by
  rw [mem_bot, B_master, ← cone_nil]
  constructor
  · exact cone_injective
  · intro h; rw [h]

end DomainTheory.Neighborhood.ExampleB
