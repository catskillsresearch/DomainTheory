/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise122
import DomainTheory.Neighborhood.Exercise213.Basic
import DomainTheory.Neighborhood.Exercise213.principalFamily_directed


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem



theorem eq_iSupDirected_principal (x : V₀.Element) :
    x = iSupDirected (fun i : {X : Set α // x.mem X} => V₀.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V₀.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V₀.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

end NeighborhoodSystem
end DomainTheory.Neighborhood
