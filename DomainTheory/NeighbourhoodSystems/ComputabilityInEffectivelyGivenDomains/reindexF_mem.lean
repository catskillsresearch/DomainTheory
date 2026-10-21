/-ai
If a singly indexed set is a neighbourhood of the iteration, then its reindexing is a neighbourhood of the double iteration.

Each inner fiber of the reindexing is a fiber of the original neighbourhood, hence a neighbourhood of the system. For each outer index those fibers equal the master neighbourhood for all sufficiently large inner indices, because the pairing grows with its second component. For all sufficiently large outer indices every inner fiber equals the master of the iteration, because the pairing grows with its first component, so the outer fiber is the master of the iteration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

theorem reindexF_mem {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    (iterSys (iterSys V)).mem (reindexF W) := by
  obtain ⟨hWf, Nw, hNw⟩ := hW
  refine ⟨fun i => ⟨fun j => ?_, Nw, fun j hj => ?_⟩, Nw, fun i hi => ?_⟩
  · -- inner fibers are `V`-neighbourhoods
    show V.mem (fiber2 (reindexF W) i j)
    rw [fiber2_reindexF]; exact hWf (Nat.pair i j)
  · -- inner cofinite-`Δ` (per `i`)
    show fiber2 (reindexF W) i j = V.master
    rw [fiber2_reindexF]
    exact hNw (Nat.pair i j) (le_trans hj (le_pair_right i j))
  · -- outer cofinite-`Δ`
    apply eq_of_fiber_eq
    intro j
    show fiber2 (reindexF W) i j = fiber ((iterSys V).master) j
    rw [fiber2_reindexF, fiber_iterSys_master]
    exact hNw (Nat.pair i j) (le_trans hi (le_pair_left i j))

end Exercise718

end DomainTheory.NeighbourhoodSystems
