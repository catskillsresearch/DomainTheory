/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.exists_mem_ne_master_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- The closed form of `check`'s elementwise action: `check(x) ∋ Y ↔ Y ∈ O ∧ (Y = {0,1} ∨ x ≠ ⊥)`.
So `check(x) = ⊥_O` when `x = ⊥_D`, and `check(x) = ⊤_O` otherwise. -/
theorem mem_toElementMap_check {x : D.Element} {Y : Set (Fin 2)} :
    (check.toElementMap x).mem Y ↔ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ x ≠ D.bot) := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hXD, hYO, hcase⟩
    refine ⟨hYO, ?_⟩
    rcases hcase with h | hXne
    · exact Or.inl h
    · refine Or.inr fun hxbot => hXne ?_
      have hxX' : x.mem X := hxX
      rw [hxbot, mem_bot] at hxX'
      exact hxX'
  · rintro ⟨hYO, hYeq | hxne⟩
    · exact ⟨D.master, x.master_mem, D.master_mem, hYO, Or.inl hYeq⟩
    · obtain ⟨X, hxX, hXne⟩ := exists_mem_ne_master_of_ne_bot hxne
      exact ⟨X, hxX, x.sub hxX, hYO, Or.inr hXne⟩

end DomainTheory.NeighbourhoodSystems
