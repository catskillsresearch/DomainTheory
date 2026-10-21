/-ai
If one set of pairs is contained in another, then each fiber of the smaller set is contained in the corresponding fiber of the larger set.

A token in the smaller fiber is a pair in the smaller set, hence a pair in the larger set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

theorem fiber_mono {W W' : Set (ℕ × α)} (h : W ⊆ W') (i : ℕ) : fiber W i ⊆ fiber W' i :=
  fun _ ha => h ha

end DomainTheory.NeighbourhoodSystems
