/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.Product
public import DomainTheory.Neighborhood.Example84.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂










theorem Otop_ne_Obot : Otop ≠ O.bot := by
  intro h
  have h1 : Otop.mem ({0} : Set (Fin 2)) := ⟨O_mem_zero, subset_rfl⟩
  rw [h, mem_bot, O_master_eq] at h1
  have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by rw [h1]; simp
  simp at h2

end DomainTheory.Neighborhood
