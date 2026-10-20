/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








/-- **Exercise 3.21.** If the output is the master, `[Y, Δ₂]` is the whole function space. -/
theorem step_master_right (Y : Set α) (hY : V₀.mem Y) :
    (step Y V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_step, Set.mem_univ, iff_true]
  exact f.mono f.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

end DomainTheory.NeighbourhoodSystems
