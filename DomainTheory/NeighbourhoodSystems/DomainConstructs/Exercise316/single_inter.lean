/-ai
The intersection of the pinnings of one copy to two sets is the pinning of that copy to the intersection of the sets.

Compare fibers. At the pinned index, each fiber is the pinned set, so the intersection of the fibers is the intersection of the sets. At every other index, each fiber is the master, and the master intersected with itself is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.eq_of_fiber_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_ne

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem single_inter {n : ℕ} (X X' : Set α) :
    single V n X ∩ single V n X' = single V n (X ∩ X') := by
  apply eq_of_fiber_eq
  intro i
  by_cases h : i = n
  · subst h; rw [fiber_inter, fiber_single_self, fiber_single_self, fiber_single_self]
  · rw [fiber_inter, fiber_single_ne h, fiber_single_ne h, fiber_single_ne h, Set.inter_self]

end DomainTheory.NeighbourhoodSystems
