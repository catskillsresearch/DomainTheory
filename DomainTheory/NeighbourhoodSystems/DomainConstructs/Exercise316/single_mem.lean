/-ai
If X is a neighbourhood, then the pinning of copy n to X is a neighbourhood of the infinite iterate.

The fiber at n is X, and every other fiber is the master, so every fiber is a neighbourhood. From n + 1 onward the index differs from n, so the fiber equals the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_ne
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- `single V n X` is a `𝒟^∞`-neighbourhood whenever `X ∈ 𝒟`. -/
theorem single_mem {n : ℕ} {X : Set α} (hX : V.mem X) : (iterSys V).mem (single V n X) := by
  refine ⟨fun i => ?_, n + 1, fun i hi => ?_⟩
  · by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact V.master_mem
  · exact fiber_single_ne (by omega : i ≠ n) X

end DomainTheory.NeighbourhoodSystems
