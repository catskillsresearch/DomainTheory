/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise115.Basic
public import DomainTheory.Neighborhood.Exercise115.flat_mem_singleton
public import DomainTheory.Neighborhood.Exercise115.flat_classify

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise115

open DomainTheory.Neighborhood NeighborhoodSystem








/-- **All elements of `flat` are finite** (principal). -/
theorem flat_all_finite (x : flat.Element) : ∃ (X : Set ℕ) (h : flat.mem X), x = flat.principal h := by
  rcases flat_classify x with rfl | ⟨n, rfl⟩
  · exact ⟨flat.master, flat.master_mem, rfl⟩
  · exact ⟨{n}, flat_mem_singleton n, rfl⟩

end DomainTheory.Neighborhood.Exercise115
