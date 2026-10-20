module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

theorem fiber_inter (W W' : Set (ℕ × α)) (i : ℕ) :
    fiber (W ∩ W') i = fiber W i ∩ fiber W' i := rfl

end DomainTheory.NeighbourhoodSystems
