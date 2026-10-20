/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise719.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)

/-- **Every member of a `ℙ𝒟`-neighbourhood is a `𝒟`-neighbourhood.** -/
theorem PDmem_mem {A : Set (Set α)} (hA : V.PDmem A) {X : Set α} (hX : X ∈ A) : V.mem X := by
  obtain ⟨L, hL, rfl⟩ := hA
  obtain ⟨X', _, hXmem, _⟩ := (V.mem_PDunion).mp hX
  exact hXmem

end NeighborhoodSystem
end DomainTheory.Neighborhood
