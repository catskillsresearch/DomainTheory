module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

@[simp] theorem mem_fiber {W : Set (ℕ × α)} {i : ℕ} {a : α} : a ∈ fiber W i ↔ (i, a) ∈ W := Iff.rfl

end DomainTheory.NeighbourhoodSystems
