/-ai
Pinning any copy to the master neighbourhood yields the master neighbourhood of the infinite iterate.

Compare fibers with those of the iterate master, each of which is the original master. At the pinned index the fiber is the master, and at every other index the pinned fiber is already the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.eq_of_fiber_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_ne
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

theorem single_master (n : ℕ) : single V n V.master = (iterSys V).master := by
  apply eq_of_fiber_eq
  intro i
  rw [fiber_iterSys_master]
  by_cases h : i = n
  · subst h; rw [fiber_single_self]
  · rw [fiber_single_ne h]

end DomainTheory.NeighbourhoodSystems
