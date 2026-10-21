/-ai
If the index i differs from n, the i-th fiber of the pinning of copy n is the master neighbourhood.

Extensionality and simplification of the fiber and the pinning use that the indices differ.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
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

theorem fiber_single_ne {n i : ℕ} (h : i ≠ n) (X : Set α) : fiber (single V n X) i = V.master := by
  ext a; simp [fiber, single, h]

end DomainTheory.NeighbourhoodSystems
