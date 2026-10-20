/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- **Exercise 1.20 — `𝒟'` is positive.** `↑X ∩ ↑Y = ↑(X∩Y)` is a neighbourhood iff it is
non-empty: a witness `Z ⊆ X ∩ Y` gives `X ∩ Y ∈ 𝒟`; conversely `↑W` always contains `W`. -/
theorem powerSystem_isPositive : V.powerSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.upSet_inter]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨W, hW, subset_rfl⟩
  · rintro ⟨Z, hZmem, hZsub⟩
    exact ⟨X ∩ Y, V.inter_mem hX hY hZmem hZsub, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
