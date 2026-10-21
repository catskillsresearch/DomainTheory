/-ai
The master neighbourhood of the infinite iterate is the set of index-token pairs whose token lies in the original master.

The identity is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

@[simp] theorem iterSys_master : (iterSys V).master = {p : ℕ × α | p.2 ∈ V.master} := rfl

end DomainTheory.NeighbourhoodSystems
