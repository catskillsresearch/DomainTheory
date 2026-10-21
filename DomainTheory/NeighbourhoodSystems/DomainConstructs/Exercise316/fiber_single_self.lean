/-ai
The n-th fiber of the pinning of copy n to a set X is X itself.

Extensionality and simplification of the fiber and the pinning give the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem fiber_single_self (n : ℕ) (X : Set α) : fiber (single V n X) n = X := by
  ext a; simp [fiber, single]

end DomainTheory.NeighbourhoodSystems
