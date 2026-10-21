/-ai
If X is contained in X', then the pinning of a copy to X is contained in the pinning of that copy to X'.

On a pair, unfold the pinning. When the index is the pinned copy, the token inclusion is the hypothesis. Otherwise both sides ask for membership in the master.
ai-/
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
