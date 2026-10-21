/-ai
Two sets of index-token pairs that have the same fiber at every index are equal.

Extensionality on a pair reduces to extensionality of the fiber at its index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

theorem eq_of_fiber_eq {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i = fiber W' i) : W = W' := by
  ext ⟨i, a⟩
  exact Set.ext_iff.mp (h i) a

end DomainTheory.NeighbourhoodSystems
