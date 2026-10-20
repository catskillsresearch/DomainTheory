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

@[expose] public section


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)




/-- **Definition 7.9 (remark 2).** "In that case `↓X ∩ ↓Y = ↓(X ∩ Y)`." When `{X, Y}` is
consistent (witness `Z ⊆ X ∩ Y`, `Z ∈ 𝒟`), the intersection `X ∩ Y` is again a neighbourhood,
so `↓X ∩ ↓Y = ↓(X ∩ Y)` is a neighbourhood of the prepared system `𝒟†`. (The unconditional set
identity `↓X ∩ ↓Y = ↓(X ∩ Y)` is Exercise 1.20's `upSet_inter`; the content here is membership
in `𝒟†`.) -/
theorem dagger_upSet_inter {X Y Z : Set α} (hX : V.mem X) (hY : V.mem Y) (hZ : V.mem Z)
    (hsub : Z ⊆ X ∩ Y) : V.dagger.mem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  exact ⟨X ∩ Y, V.inter_mem hX hY hZ hsub, rfl⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
