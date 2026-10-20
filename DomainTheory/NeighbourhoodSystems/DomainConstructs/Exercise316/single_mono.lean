module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem single_mono {n : ℕ} {X X' : Set α} (h : X ⊆ X') : single V n X ⊆ single V n X' := by
  intro p hp
  simp only [single, Set.mem_ofPred_eq] at hp ⊢
  by_cases hc : p.1 = n
  · rw [ite_eq_left hc] at hp ⊢; exact h hp
  · rw [ite_eq_right hc] at hp ⊢; exact hp

end DomainTheory.NeighbourhoodSystems
